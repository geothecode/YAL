{-#
    LANGUAGE
        OverloadedStrings,
        RecordWildCards,
        NamedFieldPuns
#-}

module Typing where

import Syntax
import Parsing                  (PE(..))

import Data.Set                 (Set)
import Data.Map                 (Map)
import Data.Text                (Text)
import Data.List                (nub)
import qualified Data.Set       as S
import qualified Data.Map       as M
import qualified Data.Text      as T

import Control.Monad    (replicateM)
import Control.Monad.State
import Control.Monad.Except

type Typer a
    = ExceptT Error (State TE) a

type Subst
    = Map TypeVar Type

type Types -- parser collects info about parsed typesignatures (dtypes)
    = Map Name Scheme

data Unique
    = Unique { counter :: Int }
    deriving (Show, Eq, Ord)

data TE
    = TE
    {
        uniq :: Unique
    ,   tenv :: Types
    ,   text :: Extensions
    ,   tdat :: [Declaration]
    ,   locl :: Types
    ,   ltyp :: Type
    ,   lpos :: Int
    ,   uvar :: Set Name
    ,   infered :: Types
    -- ,   tcon :: Map Name Type
    }
    deriving (Show, Eq, Ord)

initTE :: TE
initTE = TE
    {
        uniq = Unique 0
    ,   tenv = M.empty
    ,   text = S.empty
    ,   tdat = mempty
    ,   locl = M.empty
    ,   ltyp = NoType
    ,   lpos = 0
    ,   uvar = S.empty
    ,   infered = M.empty
    -- ,   tcon = M.empty
            --     M.insert "Nat"      (TypeConstant "Nat")    -- 1..
            -- $   M.insert "Int"      (TypeConstant "Int")    -- typical integer
            -- $   M.insert "Bool"     (TypeConstant "Bool")   -- bool
            -- $   M.empty
    }

class Substitutable a where
    apply :: Subst -> a -> a
    free  :: a -> Set TypeVar

fromPE :: PE -> TE -> TE
fromPE PE{..} TE{..} = foldl addSig (foldl extend TE{tdat = ddata, ..} (M.toList dtypes)) (M.toList sigs)

addSig :: TE -> (Name, Scheme) -> TE
addSig TE{..} (n,s) = TE{infered = M.insert n s infered, ..}

extend :: TE -> (Name, Scheme) -> TE
extend TE{..} (n,s) = TE{tenv = M.insert n s tenv, ..}

record :: (Name, Scheme) -> Typer ()
record a = do
    te <- get
    put (extend te a)

update :: Subst -> Typer ()
update s = modify (apply s)

extendl :: Types -> Typer ()
extendl s = do
    TE{..} <- get
    put TE{locl = s <> locl, ..}

inscope :: Type -> Typer ()
inscope t = do
    TE{..} <- get
    put TE{ltyp = t, lpos = 0, ..}

lnext :: Typer ()
lnext = do 
    TE{..} <- get
    put TE{lpos = lpos + 1, ..}

clearl :: Typer ()
clearl = do
    TE{..} <- get
    put TE{locl = M.empty, ltyp = NoType, lpos = 0, ..}

letters :: [Name]
letters = T.pack <$> ([1..] >>= flip replicateM ['a'..'z'])

instance {-# OVERLAPS #-}
    Semigroup Subst where
        a <> b = (apply a) <$> b `M.union` a

instance Substitutable Type where
    apply _ t@TypeConstant{} = t
    apply s t@(TypeVar a) = M.findWithDefault t a s
    apply s (a :-> b) = apply s a :-> apply s b

    free TypeConstant{} = mempty
    free (TypeVar a) = S.singleton a
    free (a :-> b) = free a `S.union` free b

instance Substitutable Scheme where
    apply s (Forall cs t) = Forall cs (apply s' t)
        where s' = foldr M.delete s cs
    free (Forall cs t) = free t `S.difference` S.fromList cs

instance Substitutable a => 
    Substitutable [a] where
        apply = fmap . apply

        free = foldr (S.union . free) mempty

instance Substitutable TE where
    apply s TE{..} = TE{tenv = apply s <$> tenv, ..}

    free TE{..} = free (M.elems tenv)

uGet :: Typer Int
uGet = do
    TE{uniq = Unique a, ..} <- get
    put TE{uniq = Unique (a + 1), ..}
    return a

fresh :: Typer Type
fresh = do
    n <- uGet
    return (TypeVar (TVar (letters !! n)))

occurs :: Substitutable a => TypeVar -> a -> Bool
occurs t s = S.member t (free s)

unify :: Type -> Type -> Typer Subst
unify (TypeConstant a) (TypeConstant b) | a == b = return mempty
unify (TypeVar a) t = bind a t
unify t (TypeVar a) = bind a t
unify (al :-> bl) (ar :-> br) = do
    s1 <- unify al ar
    s2 <- unify (apply s1 bl) (apply s1 br)
    return (s2 <> s1)
unify a b = throwError (UnificationFail a b)

bind :: TypeVar -> Type -> Typer Subst
bind t s | TypeVar t == s = return mempty
         | occurs t s = throwError (InfiniteType t s)
         | otherwise = return (M.singleton t s)

instantiate :: Scheme -> Typer Type
instantiate (Forall ts t) = do
    nts <- mapM (const fresh) ts
    let s = M.fromList (zip ts nts)
    return (apply s t)

generalize :: Type -> Typer Scheme
generalize t = do
    te <- get
    let ts = S.toList (S.difference (free t) (free te))
    return (Forall ts t)

lookupEnv :: Name -> Types -> Typer (Maybe (Subst, Type))
lookupEnv a t = do
    TE{..} <- get
    case M.lookup a t of
        Just sc -> do
            t <- instantiate sc
            return (Just (mempty, t))
        Nothing -> return Nothing

sizeT :: Type -> Int
sizeT (_ :-> b) = 1 + sizeT b
sizeT _ = 1

-- fromPattern :: Pattern -> Name
-- fromPattern (VariableP name) = name

-- collect' :: Pattern -> Type -> Typer (Subst, Maybe Type)
-- collect' x (a :-> b) | sizeT b > 1 = do
--     return (M.singleton (fromPattern x) a, return b)
-- collect' _  _ = return (mempty, Nothing)

-- collect :: [Pattern] -> Type -> Typer Subst
-- collect a b | length a >= sizeT b = 
-- collect [] _ = return mempty
-- collect _ a | sizeT a == 1 = return mempty
-- collect (p:ps) t = do
--     (s1, typ) <- collect' p t
--     v <- case typ of
--         Just a -> return a
--     s2 <- collect ps v
--     return (s2 <> s1)

facecontrol :: Pattern -> Typer Types
facecontrol WildcardP = lnext >> return mempty
facecontrol LiteralP{} = lnext >> return mempty
facecontrol (DataConstructorP _ []) = lnext >> return mempty
facecontrol (DataConstructorP n args) = do
        oldt <- gets ltyp
        (_, t) <- inferExpr (Var n)
        inscope t
        let 
            has  = length args
            need = sizeT t - 1
        if has == need 
            then (mapM facecontrol args) >> inscope oldt >> return mempty
            else throwError (ShouldHaveArgs need has)
facecontrol (VariableP n) = do
    checkThenAdd n
    t <- gets ltyp
    p <- gets lpos
    sc <- generalize (thead (toListT' t !! p))
    lnext
    extendl (M.singleton n sc)
    return mempty



checkThenAdd :: Name -> Typer ()
checkThenAdd name = do
    TE{..} <- get
    if name `S.member` uvar
        then throwError (MultipleDeclaration name)
        else put TE{uvar = name `S.insert` uvar, ..} 

toListT' :: Type -> [Type]
toListT' (a :-> b) = [a] <> toListT' b
toListT' _ = []

collect :: [Pattern] -> Typer Types
collect p = (mapM facecontrol p) >> return mempty -- TODO:

-- TODO:
-- make local-scope environent in TE to accumulate things line this: data A = A Int; f (A a) = a -- to guess that a :: Int

-- lookupLocl :: Name -> Typer (Maybe (Subst, Type))
-- lookupLocl a = do
--     TE{..} <- get
--     case M.lookup a locl of
--         Just t -> do
--             t1 <- generalize t
--             return (Just (mempty, t1))
--         Nothing -> return Nothing

domain :: Type -> Type
domain (_ :-> a) = domain a
domain t@TypeVar{} = t
domain t@TypeConstant{} = t

thead :: Type -> Type
thead (a :-> _) = a
thead a = a


inferExpr :: Expr -> Typer (Subst, Type)
inferExpr e = do
    TE{..} <- get
    case e of
        Var a -> do
            r <- lookupEnv a tenv
            case r of
                Just t -> return t
                Nothing -> do
                    l <- lookupEnv a locl
                    case l of
                        Just t -> return t
                        Nothing -> throwError (UnboundVariable a)

        Constructor a -> inferExpr (Var a)

        Lam a e -> do
            tv <- fresh
            case a of
                VariableP n -> do
                    record (n, Forall [] tv)
                    (s, t) <- inferExpr e
                    return (s, apply s tv :-> t)
                LiteralP n -> do
                    (_, lt) <- inferExpr (Lit n)
                    (s, t) <- inferExpr e
                    return (s, lt :-> t)
                WildcardP -> do
                    (s, t) <- inferExpr e
                    return (s, tv :-> t)
                d@(DataConstructorP name _) -> do
                    facecontrol d
                    (_, nt) <- inferExpr (Var name)
                    inscope nt
                    (s, t) <- inferExpr e
                    clearl
                    return (s, domain nt :-> t)
                -- LiteralP x -> do
                --     (s, t) <- inferExpr (Lit x)
                --     record (n, Forall [] t)
                --     update s
                --     unify t tv
                -- DataConstructorP name args -> do
                --     (s, t) <- inferExpr (Var name)
                --     s1 <- collect args t
                --     extendl s1
                --     s2 <- unify t tv
                --     return s2
                -- _ -> return mempty
            -- sub <- fromPattern a
            -- (s, t) <- inferExpr e
            
            -- return (s, apply (s <> sub) tv :-> t)

        Let a l r -> do
            (s1, t1) <- inferExpr l
            update s1
            t1' <- generalize t1
            record (a, t1')
            (s2, t2) <- inferExpr r
            return (s2 <> s1, t2) 

        App l r -> do
            tv <- fresh
            (s1, t1) <- inferExpr l
            update s1
            (s2, t2) <- inferExpr r
            s3 <- unify (apply s2 t1) (t2 :-> tv)
            return (s3 <> s2 <> s1, apply s3 tv)

        If a l r -> do
            (s1, t1) <- inferExpr a
            (s2, t2) <- inferExpr l
            (s3, t3) <- inferExpr r
            s4 <- unify t1 tBool
            s5 <- unify t2 t3
            return (s5 <> s4 <> s3 <> s2 <> s1, apply s5 t2)
        
        Fix a -> do
            tv <- fresh
            (s1, t1) <- inferExpr a
            s2 <- unify (tv :-> tv) t1
            return (s2 <> s1, apply s2 tv)
        
        -- TODO: all type inferences

        i@(Infix _ _ _) -> inferExpr (fromFixity i)
        i@(Postfix _ _) -> inferExpr (fromFixity i)

        Lit (Number _) -> return (mempty, tInt)
        Lit (Character _) -> return (mempty, tChar)
        Lit (Text _) -> return (mempty, tText)

inferDecl :: Declaration -> Typer (Subst, Type)
inferDecl decl = case decl of
    Const a e -> do
            tv <- fresh
            record (a, Forall [] tv)
            (s1, t1) <- inferExpr e
            s2 <- unify (apply s1 tv) t1
            t <- generalize (apply (s2 <> s1) t1)
            record (a, t)
            extendInfered (a, t)
            return (s2 <> s1, apply (s2 <> s1) t1)
    
    Meta _ -> return (mempty, tMeta)
    
    TypeOf a t -> do
            record (a, t)
            return (mempty, NoType)

    _ -> return (mempty, NoType)

inferMany :: [Expr] -> Typer [(Subst, Type)]
inferMany = mapM inferExpr

normalize :: Scheme -> Typer Scheme
normalize f@(Forall ts t) = do
    typ <- norm t
    return (Forall (snd <$> tv) typ)
    where
        tv = zip (S.toList (free f)) (TVar <$> letters)
        norm (TypeConstant a) = return (TypeConstant a)
        norm (TypeVar a) = case lookup a tv of
            Just x -> return (TypeVar x)
            Nothing -> throwError (NotInSignature a)
        norm (a :-> b) = do
            l <- norm a 
            r <- norm b
            return (l :-> r)

closeOver :: Typer (Subst, Type) -> Typer Scheme
closeOver a = do
    (s, t) <- a
    sc <- generalize (apply s t)
    normalize sc

runInfer :: Typer (Subst, Type) -> Either Error Scheme
runInfer a = evalState (runExceptT (closeOver a)) initTE

fromFixity :: Expr -> Expr
fromFixity (Infix a l r) = App (App (Var a) l) r
fromFixity (Postfix a e) = App (Var a) e

tBool, tInt, tChar, tText, tMeta :: Type
tBool = TypeConstant "Bool"
tInt = TypeConstant "Int"
tChar = TypeConstant "Char"
tText = TypeConstant "Text"
tMeta = TypeConstant "Meta"

inferProgram :: Program -> Typer [(Subst, Type)]
inferProgram = mapM inferDecl

extendInfered :: (Name, Scheme) -> Typer ()
extendInfered (n,s) = do
    TE{..} <- get
    case M.lookup n infered of
        Just t -> do
            cond1 <- t `equivalentScheme` s
            if cond1
                then do
                    cond2 <- t `mcsc` s
                    if cond2
                        then put TE{..}
                        else put TE{infered = M.insert n s infered, ..}
                else throwError (TypesMismatch n t s)
        Nothing -> put TE{infered = M.insert n s infered, ..}

toListT :: Type -> [Type]
toListT (a :-> b) = toListT a <> toListT b
toListT a = [a]

equivalentScheme :: Scheme -> Scheme -> Typer Bool
equivalentScheme (Forall _ a) (Forall _ b) = softpriority a b

softpriority :: Type -> Type -> Typer Bool
softpriority a b =
    case (a, b) of
        (l@TypeArrow{}, r@TypeArrow{}) -> and <$> zipWithM softpriority (toListT l) (toListT r)
        (TypeVar _, TypeVar _) -> return True -- same thing
        (TypeVar _, _) -> return True -- specialization
        (a, t@(TypeVar _)) -> do
            sub <- unify a t
            update sub
            return True -- can't pass because more general
        (l@TypeConstant{}, r@TypeConstant{}) | l == r -> return True
        (_, _) -> return False

mcsc :: Scheme -> Scheme -> Typer Bool
mcsc (Forall _ a) (Forall _ b) = mostCommonType a b

mostCommonType :: Type -> Type -> Typer Bool -- checks whether first argument is the most common type
mostCommonType a b =
    case (a, b) of
        (l@TypeArrow{}, r@TypeArrow{}) -> or <$> zipWithM mostCommonType (toListT l) (toListT r)
        (TypeVar _, TypeVar _) -> return False -- same thing
        (TypeVar _, _) -> return False -- specialization
        (_, TypeVar _) -> return True -- can't pass because more general
        (l@TypeConstant{}, r@TypeConstant{}) | l == r -> return False
        (_, _) -> return False