{-#
    LANGUAGE
        OverloadedStrings,
        RecordWildCards,
        NamedFieldPuns
#-}

module Constraint where

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
    = ExceptT TypeCheckerError (State TE) a

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
fromPE PE{..} TE{..} = foldl extend TE{tdat = ddata, ..} (M.toList dtypes)

extend :: TE -> (Name, Scheme) -> TE
extend TE{..} (n,s) = TE{tenv = M.insert n s tenv, ..}

record :: (Name, Scheme) -> Typer ()
record a = do
    te <- get
    put (extend te a)

update :: Subst -> Typer ()
update s = modify (apply s)

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

lookupEnv :: Name -> Typer (Maybe (Subst, Type))
lookupEnv a = do
    TE{..} <- get
    case M.lookup a tenv of
        Just sc -> do
            t <- instantiate sc
            return (Just (mempty, t))
        Nothing -> return Nothing

infer :: Expr -> Typer (Subst, Type)
infer e = do
    TE{..} <- get
    case e of
        Var a -> do
            r <- lookupEnv a
            case r of
                Just t -> return t
                Nothing -> throwError (UnboundVariable a)

        Lam a e -> do
            tv <- fresh
            record (a, Forall [] tv)
            (s, t) <- infer e
            return (s, apply s tv :-> t)
        
        Let a l r -> do
            (s1, t1) <- infer l
            update s1
            t1' <- generalize t1
            record (a, t1')
            (s2, t2) <- infer r
            return (s2 <> s1, t2) 

        App l r -> do
            tv <- fresh
            (s1, t1) <- infer l
            update s1
            (s2, t2) <- infer r
            s3 <- unify (apply s2 t1) (t2 :-> tv)
            return (s3 <> s2 <> s1, apply s3 tv)

        If a l r -> do
            (s1, t1) <- infer a
            (s2, t2) <- infer l
            (s3, t3) <- infer r
            s4 <- unify t1 tBool
            s5 <- unify t2 t3
            return (s5 <> s4 <> s3 <> s2 <> s1, apply s5 t2)
        
        Fix a -> do
            tv <- fresh
            (s1, t1) <- infer a
            s2 <- unify (tv :-> tv) t1
            return (s2 <> s1, apply s2 tv)
        
        -- TODO: all type inferences

        Decl (Const a e) -> do
            (s1, t1) <- infer e
            t <- generalize t1
            record (a, t)
            update s1
            return (mempty, t1)
        
        Decl _ -> return (mempty, NoType)

        Meta _ -> return (mempty, tMeta)

        TypeOf a t -> do
            record (a, t)
            return (mempty, NoType)

        Pragma _ -> return (mempty, NoType)

        i@(Infix _ _ _) -> infer (fromFixity i)
        i@(Postfix _ _) -> infer (fromFixity i)

        Lit (Number _) -> return (mempty, tInt)
        Lit (Character _) -> return (mempty, tChar)
        Lit (Text _) -> return (mempty, tText)

inferMany :: [Expr] -> Typer [(Subst, Type)]
inferMany = mapM infer

fromFixity :: Expr -> Expr
fromFixity (Infix a l r) = App (App (Var a) l) r
fromFixity (Postfix a e) = App (Var a) e

tBool, tInt, tChar, tText, tMeta :: Type
tBool = TypeConstant "Bool"
tInt = TypeConstant "Int"
tChar = TypeConstant "Char"
tText = TypeConstant "Text"
tMeta = TypeConstant "Meta"
