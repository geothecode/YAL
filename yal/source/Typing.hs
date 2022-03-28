{-#
    LANGUAGE
        OverloadedStrings
#-}

module Typing where

import Syntax

-- | Debug
import Debug
import Pretty
import Text.PrettyPrint hiding ((<>))

import Data.Set                 (Set)
import Data.Map                 (Map)
import Data.Text                (Text)
import Data.List                (nub, groupBy, sortBy)
import qualified Data.Set       as S
import qualified Data.Map       as M
import qualified Data.Text      as T

import Control.Monad    (replicateM)
import Control.Monad.RWS
import Control.Monad.Except
import Data.Maybe (fromMaybe)

type Typer a
    = RWST
        (Schemes, Types)
        [Constraint]
        TE
        (Except Error)
        a

type Solver a
    = Except Error a

type Unifier
    = (Subst, [Constraint])

type Constraint
    = (Type, Type)

type Subst
    = Map Type Type

type Schemes -- parser collects info about parsed typesignatures (dtypes)
    = Map Name Scheme

type Types
    = Map Name Type

extendSchemes :: Schemes -> (Name, Scheme) -> Schemes
extendSchemes env (a,b) = M.insert a b env

adjustSchemes :: Schemes -> Schemes -> Schemes
adjustSchemes a b = M.union a b

data    TE
    =   TE
    {
        infered :: Schemes
    ,   counter :: Int
    }

deftyps :: Schemes
deftyps = 
        M.insert "print" (Forall [TVar "a"] ((TypeVar (TVar "a")) :-> TypeConstant "IO"))
    $   M.singleton "undefined" (Forall [TVar "a"] (TypeVar (TVar "a")))

instance Monoid TE where
    mempty = TE
        {
            infered = deftyps
        ,   counter = 0
        }

instance Semigroup TE where
    (<>) = adjustTE

adjustTE :: TE -> TE -> TE
adjustTE te1 te2 = te2 {infered = (infered te1) <> (infered te2)}

class Substitutable a where
    apply :: Subst -> a -> a
    free  :: a -> Set TypeVar

instance Substitutable Type where
    apply _ tc@TypeConstant{} = tc
    apply s (l :-> r) = apply s l :-> apply s r
    apply s t = M.findWithDefault t t s

    free TypeConstant{} = mempty
    free (TypeVar a) = S.singleton a
    free (l :-> r) = free l `S.union` free r

instance Substitutable Scheme where
    apply s (Forall as t) = Forall as (apply s' t)
        where s' = foldr M.delete s (TypeVar <$> as)
    
    free (Forall as t) = free t `S.difference` S.fromList as

instance Substitutable Constraint where
    apply s (l, r) = (apply s l, apply s r)

    free (l, r) = free l `S.union` free r

instance Substitutable a => Substitutable (Map Name a) where
    apply s env = M.map (apply s) env

    free env = free (M.elems env)

instance Substitutable a => Substitutable [a] where
    apply = map . apply

    free = foldr (S.union . free) mempty

instance Substitutable () where
    apply _ _ = ()

    free = mempty

-- | Typing

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Typer Type
fresh = do
    s <- get
    put (s {counter = (counter s) + 1})
    return (TypeVar (TVar (T.pack (letters !! counter s))))

instantiate :: Scheme -> Typer Type
instantiate (Forall as t) = do
    as' <- mapM (const fresh) as
    let s = M.fromList (zip (TypeVar <$> as) as')
    return (apply s t)

generalize :: Schemes -> Type -> Scheme
generalize env t = Forall as t
    where
        as = S.toList (free t `S.difference` free env)

lookupEnv :: Name -> Typer Type
lookupEnv a = do
    (sc, ts) <- ask
    infered <- gets infered
    case M.lookup a ts of
        Just t -> return t
        Nothing -> case M.lookup a sc of
                        Just t -> instantiate t
                        Nothing -> case M.lookup a infered of 
                            Just t -> instantiate t
                            Nothing -> throwError (UnboundVariable a)

inEnvS :: (Name, Scheme) -> Typer a -> Typer a
inEnvS (a,b) m = local (\(x, y) -> ((M.insertWith const a b x), y)) m

inEnvS' :: Schemes -> Typer a -> Typer a
inEnvS' ts m = local (\(x, y) -> (M.unionWith const ts x, y)) m

inEnvT :: (Name, Type) -> Typer a -> Typer a
inEnvT (a,b) m = local (\(x, y) -> (x, M.insertWith const a b y)) m

inEnvT' :: Types -> Typer a -> Typer a
inEnvT' ts m = local (\(x, y) -> (x, M.unionWith const ts y)) m

fromFixity :: Expr -> Expr
fromFixity (Infix a l r) = App (App (Var a) l) r
fromFixity (Postfix a e) = App (Var a) e

domain :: Type -> Type
domain (_ :-> a) = domain a
domain t@TypeVar{} = t
domain t@TypeConstant{} = t

thead :: Type -> Type
thead (a :-> _) = a
thead a = a

toListT :: Type -> [Type]
toListT (a :-> b) = [a] <> toListT b
toListT _ = []

toListT' :: Type -> [Type]
toListT' (a :-> b) = [a] <> toListT b
toListT' a = return a

tInt, tChar, tBool, tText :: Type
tInt = TypeConstant "Int"
tChar = TypeConstant "Char"
tBool = TypeConstant "Bool"
tText = TypeConstant "Text"

inferExpr :: Expr -> Typer Type
inferExpr e = case e of
    Lit (Number _) -> return tInt
    Lit (Character _) -> return tChar

    Var a -> lookupEnv a

    Lam pat e -> inferAlt (return pat, Nothing, e)

    Let (Const name alt) c -> do
        t1 <- inferAlt alt
        e <- asks fst
        let sc = generalize e t1
        inEnvS (name, sc) (inferExpr c)

    Con n -> inferExpr (Var n)

    App a b -> do
        t1 <- inferExpr a
        t2 <- inferExpr b
        tv <- fresh
        unify t1 (t2 :-> tv)
        return tv

    If c a b -> do
        t1 <- inferExpr c
        t2 <- inferExpr a
        t3 <- inferExpr b
        unify t1 tBool
        unify t2 t3
        return t2

    Case exps alts -> do
        ts1 <- mapM inferExpr exps
        ts2 <- mapM inferAlt alts
        case allSame ts2 of
            Nothing -> do
                let t = head ts2
                matchTypes (toType ts1) t
            Just t -> throwError (Mismatch "case" (head ts2) t)
    
    i@(Infix{}) -> inferExpr (fromFixity i)
    i@(Postfix{}) -> inferExpr (fromFixity i)

infix 4 ===
(===) :: Type -> Type -> Bool
a@TypeConstant{} === b@TypeConstant{} | a == b = True
TypeVar{} === TypeVar{} = True
TypeVar{} === TypeConstant{} = True
TypeConstant{} === TypeVar{} = True
(a:->b) === (c:->d) = a === c && b === d
a === b = False

allSame :: [Type] -> Maybe Type
allSame [] = Nothing
allSame (x:[]) = Nothing
allSame (x:xs) = case filter (\a -> not $ a === x) xs of
    [] -> Nothing
    (x:_) -> Just x 

toType :: [Type] -> Type
toType (t:[]) = t
toType (t:ts) = t :-> toType ts

matchTypes :: Type -> Type -> Typer Type
matchTypes (a :-> b) (c :-> d) = do
    unify a c
    matchTypes b d
matchTypes a (b :-> c) = do
    unify a b
    return c

inferPattern :: Pattern -> Typer (Maybe Types, Type)
inferPattern pat = do
    tv <- fresh
    let (TypeVar tv') = tv
    case pat of
        VarP n -> return (Just $ M.singleton n tv, tv)
        LitP n -> do
            t <- inferExpr (Lit n)
            return (Nothing, t)
        WildP -> return (Nothing, tv)
        ConP n pats -> do
            tpats <- mapM inferPattern pats
            let typs = snd <$> tpats
                tvars = foldl M.union mempty $ fromMaybe mempty . fst <$> tpats
            cont <- inferExpr (Var n)
            zipWithM unify typs (toListT cont)
            return (Just tvars, domain cont)


inferAlt :: Syntax.Alt -> Typer Type
inferAlt (pats, cond, e) = do
    tpats <- mapM inferPattern pats
    let typs = snd <$> tpats
        tvars = foldl M.union mempty $ fromMaybe mempty . fst <$> tpats
    case cond of
        Just ex -> do
            t <- inEnvT' tvars (inferExpr ex)
            unify t tBool
        Nothing -> return ()
    t <- inEnvT' tvars (inferExpr e)
    return (foldr (:->) t typs)

inferDecl :: Declaration -> Typer ()
inferDecl (Const name alt) = do
    g <- get
    tv <- fresh
    case runTyper'' (inEnvT (name, tv :-> tv) (inferAlt alt)) g of
        Left err -> throwError err
        Right (typ, _, _) -> do
            unify typ (tv :-> tv)
            let sc@(Forall _ sct) = generalize (infered g) typ
            case M.lookup name (infered g) of
                Just sc'@(Forall _ sc't) -> do
                    s <- checkGenerality name sct sc't
                    return ()
                Nothing -> put (g {infered = M.insertWith const name sc (infered g)})
inferDecl (TypeOf name sc) = do
    modify (\g -> g {infered = M.insertWith const name sc (infered g)})
inferDecl _ = return ()

inferDecls :: [Declaration] -> Typer ()
inferDecls ds = mapM inferDecl ds >> return ()

normalize :: Scheme -> Typer Scheme
normalize sc@(Forall _ t) = do
    typ <- norm t
    return (Forall (snd <$> tv) typ)
    where
        tv = zip (S.toList (free sc)) (TVar <$> T.pack <$> letters)

        norm t@TypeConstant{} = return t
        norm (TypeVar a) =
            case lookup a tv of
                Just tv -> return (TypeVar tv)
                Nothing -> throwError (NotInSignature a)
        norm (a :-> b) = do
            l <- norm a
            r <- norm b
            return (l :-> r)
            
closeOver :: Type -> Typer Scheme
closeOver = normalize . generalize mempty

checkGenerality :: Name -> Type -> Type -> Typer Type
checkGenerality _ a@TypeVar{} TypeVar{} = return a
checkGenerality _ a@TypeConstant{} TypeVar{} = return a
checkGenerality _ a@TypeConstant{} b@TypeConstant{} | a == b = return a
checkGenerality n (q :-> w) (e :-> r) = do
    a <- checkGenerality n q e
    b <- checkGenerality n w r
    return (a :-> b)
-- checkGenerality name a@TypeVar{} b@TypeConstant{} = throwError (MoreGeneral name a b)
checkGenerality name a@TypeVar{} b@TypeConstant{} = return b
checkGenerality name a b = throwError (Mismatch name a b) -- if types aren't equal

-- | Constraints

instance {-# OVERLAPS #-} Semigroup Subst where
    -- a <> b = M.fromList $ concat $ zipWith genSub (M.toList (apply a <$> b)) (M.toList a) 
    a <> b = M.fromList $ mkLegal <$> go ((M.toList (apply a <$> b)) <> (M.toList a))
    -- a <> b = M.union (apply a <$> b) a

mkLegal :: (Type, Type) -> (Type, Type)
mkLegal (a@TypeConstant{}, b@TypeVar{}) = (b, a)
mkLegal (a@TypeArrow{}, b@TypeArrow{}) = (a, b)
mkLegal (a@TypeArrow{}, b) = (b, a)
mkLegal c = c

go :: Eq a => [(a,a)] -> [(a,a)] 
go xs = concat $ (\a -> if length a > 1 then pairs $ snd <$> a else a) <$> groupBy (\a b -> fst a == fst b) xs

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = fmap (x,) xs <> pairs xs


unify :: Type -> Type -> Typer ()
unify a b = tell [(a, b)]

unifyMany :: [Type] -> [Type] -> Solver Subst
unifyMany [] [] = return mempty
unifyMany (t1:ts1) (t2:ts2) = do
    s1 <- unifies t1 t2
    s2 <- unifyMany ts1 ts2
    return (s1 <> s2)
unifyMany t1 t2 = throwError (UnificationFail (arr t1) (arr t2))
    where
        arr (t:[]) = t
        arr (t:ts) = t :-> arr ts

unifies :: Type -> Type -> Solver Subst
unifies t1 t2 | t1 == t2 = return mempty
unifies (TypeVar v) t = bind v t
unifies t (TypeVar v) = bind v t
unifies (q :-> w) (e :-> r) = unifyMany [q,w] [e,r]
unifies t1 t2 = throwError (UnificationFail t1 t2)

bind :: TypeVar -> Type -> Solver Subst
bind v t | t == TypeVar v = return mempty
         | occurs v t = throwError (InfiniteType v t)
         | otherwise = return (M.singleton (TypeVar v) t)

occurs :: Substitutable a => TypeVar -> a -> Bool
occurs v a = v `S.member` free a

solver :: Unifier -> Solver Subst
solver (sub, cs) =
    case cs of
        [] -> do
            let m = M.toList sub
            if finished m 
                then return sub
                else solver (mempty, m)
        ((t1,t2):ts) -> do
            s <- unifies t1 t2
            solver (s <> sub, apply s ts)
        -- ts -> do
        --     s <- mconcat <$> mapM (\(a,b) -> unifies a b) ts
        --     solver (s <> sub, mempty)

finished :: [(Type, Type)] -> Bool
finished t = and $ go <$> t
    where
        go (TypeArrow{}, _) = False
        go _ = True

-- | Finishing

preludeEnv = M.fromList [("*",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Int")))),("+",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Int")))),("-",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Int")))),("/",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Int")))),("<",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Bool")))),("<=",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Bool")))),("<>",Forall [] (TypeArrow (TypeConstant "Text") (TypeArrow (TypeConstant "Text") (TypeConstant "Text")))),("==",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Bool")))),(">",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Bool")))),(">=",Forall [] (TypeArrow (TypeConstant "Int") (TypeArrow (TypeConstant "Int") (TypeConstant "Bool")))),("False",Forall [] (TypeConstant "Bool")),("TextCons",Forall [] (TypeArrow (TypeConstant "Char") (TypeArrow (TypeConstant "Text") (TypeConstant "Text")))),("TextNil",Forall [] (TypeConstant "Text")),("True",Forall [] (TypeConstant "Bool")),("print",Forall [TVar "a"] (TypeArrow (TypeVar (TVar "a")) (TypeConstant "IO"))),("undefined",Forall [TVar "a"] (TypeVar (TVar "a"))), ("$", Forall [TVar "a", TVar "b"] ((tv "a" :-> tv "b") :-> tv "a" :-> tv "b"))]

runSolver :: [Constraint] -> Either Error Subst
runSolver cs = runExcept $ solver (mempty, cs)

getConstraints :: Typer a -> Either Error [Constraint]
getConstraints t = customRunTyper t ((\a g -> g {infered = a}) preludeEnv mempty) >>= (\(_,_,c)-> return c)

getConstraints' :: Typer a -> Schemes -> Either Error [Constraint]
getConstraints' t scs = customRunTyper t ((\a g -> g {infered = a}) scs mempty) >>= (\(_,_,c)-> return c)

runTyper' :: Typer a -> Either Error (a, TE, [Constraint])
runTyper' typer = runExcept (runRWST typer mempty mempty)

customRunTyper :: Typer a -> TE -> Either Error (a, TE, [Constraint])
customRunTyper typer te = runExcept (runRWST typer mempty te)

runTyper'' :: Substitutable a => Typer a -> TE -> Either Error (a, TE, [Constraint])
runTyper'' typer te = 
    case customRunTyper typer te of
        Left err -> Left err
        Right (t, te, cs) -> 
            case runSolver cs of
                Left err -> Left err
                Right sub -> 
                    Right ((apply sub t), te, cs)
                    -- case runTyper' (closeOver (apply sub t)) of
                    --     Left err -> Left err
                    --     Right (sc, _, _) -> Right sc

runTyper :: Substitutable a => Typer a -> TE -> Either Error (a, TE)
runTyper t te = (\(a,b,_) -> (a,b)) <$> runTyper'' t te

instance Pretty Constraint where
    pretty n (t1, t2) = pretty n t1 <+> "=" <+> pretty n t2

dbg :: (Substitutable a, Show a) => Typer a -> IO ()
dbg typer = case runTyper'' typer ((\a g -> g {infered = a}) preludeEnv mempty) of
    Left err -> print err
    Right (a, te, cs) -> do
        putStrLn $ show a
        -- print (infered te)
        mapM putStrLn (runPretty <$> cs) >> return ()
        putStrLn $ show (runSolver cs)

d cs = do
    putStrLn"constraints:"
    mapM putStrLn (runPretty <$> cs)
    putStrLn "pre-solved:"
    mapM putStrLn (runPretty <$> go cs)
    putStrLn "solved:"
    mapM putStrLn (runPretty <$> (M.toList $ case runSolver cs of Right x -> x))
    return ()

getScheme :: Typer Type -> Typer Scheme
getScheme typ = do
    e <- get
    case customRunTyper typ e of
        Left err -> throwError err
        Right (t, te, cs) -> do
            case runSolver cs of
                Left err -> throwError err
                Right sub -> closeOver (apply sub t)


runTyperV :: Typer () -> Either Error TE
runTyperV t = case runTyper' t of
    Right (_, te, _) -> Right te
    Left err -> Left err

typerStepD :: Declaration -> Typer ()
typerStepD decl = inferDecl decl

typerStepE :: Expr -> Typer Scheme
typerStepE e = do
    env <- gets infered
    t <- inferExpr e
    return (generalize env t)

fromSchemes :: Schemes -> TE -> TE
fromSchemes sc te = te {infered = sc <> (infered te)}