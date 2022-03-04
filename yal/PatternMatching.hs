module PatternMatching where

import Syntax

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M


type Matcher = ExceptT MatcherError (State Env) Bool

-- NF stands for normal form

match :: (Pattern, Value) -> Matcher
match (p, v) = case p of
    WildcardP -> return True
    
    DataConstructorP
        name args -> case v of
            C name' args' -> if name == name' 
                then do
                    let 
                        l1 = (length args)
                        l2 = (length args')
                    if l1 == l2
                        then and <$> mapM match (zip args args')
                    else throwError (ShouldHaveArgs name l2 l1)
                else return False
            _ -> return False
    
    VariableP name -> do
        modify (M.singleton name v <>)
        return True
    
    LiteralP lit -> case v of
        Lt lit' -> return (lit == lit')

        _ -> return False
