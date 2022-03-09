module PatternMatching where

import Syntax

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M


type Matcher = ExceptT Error (State Env) Bool

initEnv :: Env
initEnv = M.empty

-- NF stands for normal form

match :: Pattern -> Value -> Matcher
match p v = case p of
    WildcardP -> return True
    
    DataConstructorP
        name args -> case v of
            ConV name' args' -> if name == name' 
                then do
                    let 
                        has = (length args')
                        need = (length args)
                    if need == has
                        then and <$> (zipWithM match args args')
                    else throwError (ShouldHaveArgs has need)
                else return False
            _ -> return False
    
    VariableP name -> do
        modify (M.singleton name v <>)
        return True
    
    LiteralP lit -> case v of
        LitV lit' -> return (lit == lit')

        _ -> return False

runMatcher :: Matcher -> (Either Error Bool, Env)
runMatcher m = runState (runExceptT m) initEnv