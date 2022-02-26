{-#
    LANGUAGE
        OverloadedStrings,
        RecordWildCards,
        NamedFieldPuns
#-}

module Typing where

import Syntax
import Parsing          (PE(..))

import Data.Set         (Set)
import Data.Map         (Map)
import Data.List        (nub)
import qualified Data.Set as S
import qualified Data.Map as M

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

