{-#
    LANGUAGE
        OverloadedStrings,
        RecordWildCards,
        NamedFieldPuns
#-}

module Evaluation where

import Parsing
import Typing
import Syntax
import PatternMatching

import Text.Megaparsec hiding (State, match)
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

type Alt = (Pattern, Expr)

type Eval a = ExceptT Error (State Global) a

data Global
    = Global
    {
        vars :: Map Name Value
    ,   names :: Set Name
    ,   tomatch :: Maybe Value
    -- ,   main :: Bool -- is there a main function
    }
    deriving (Show, Eq, Ord)

initGlobal :: Global
initGlobal 
    = Global
    {
        vars = M.empty
    ,   names = S.empty
    ,   tomatch = Nothing
    }

checkOccurence :: Name -> Eval ()
checkOccurence name = do
    Global{..} <- get
    if name `S.member` names
        then throwError (MultipleDeclaration name)
        else put Global{names = name `S.insert` names, ..} 

evalIO :: IO ()
evalIO = do
    line@(l:ls) <- getLine
    case exec pSource (T.pack line) of
        (Right e, pe) -> 
            case runState (runExceptT (inferProgram e)) (fromPE pe initTE) of
                (Right t ,_) -> print t

evalProgram :: Program -> Eval Value
evalProgram = undefined

evalOne :: Declaration -> Eval Value
evalOne decl = do
    case decl of
        Const name expr -> do
            checkOccurence name
            e <- evalExpr expr
            return e

add :: Name -> Value -> Eval ()
add n v = do
    Global{..} <- get
    put Global{vars = M.insert n v vars, ..}

find :: Name -> Eval Value
find name = do
    vars <- gets vars
    case M.lookup name vars of
        Nothing -> throwError (NoSuchVariable name)
        Just v -> return v

emplace :: Value -> Eval ()
emplace v = do
    Global{..} <- get
    put Global{tomatch = return v, ..}

clear :: Eval ()
clear = do
    Global{..} <- get
    put Global{tomatch = Nothing, ..}

evalExpr :: Expr -> Eval Value
evalExpr e = do
    case e of
        App a b -> do
            eb <- evalExpr b
            emplace eb
            ea <- evalExpr a
            clear
            return ea
        Lam pat e -> do
            v <- gets tomatch
            case v of
                Nothing -> undefined  
                Just val -> do
                    case runMatcher (match pat val) of
                        (Right True, env) -> return (LamV env e)
                        (Left err, _) -> throwError err
        Var n -> find n
        Constructor n -> return (ConV n [])
        Let n e1 e2 -> do
            ee1 <- evalExpr e1
            return (LamV (M.singleton n ee1) e2)
        Lit l -> return (LitV l)
        If c e1 e2 -> do
            cond <- evalExpr c
            if cond == (ConV "True" [])
                then evalExpr e1
                else evalExpr e2

runEval :: Eval Value -> (Either Error Value, Global)
runEval e = runState (runExceptT e) initGlobal

evio :: IO ()
evio = do
    l <- getLine
    case exec pSource (T.pack l) of
        (Right e, pe) -> 
            case runState (runExceptT (inferProgram e)) (fromPE pe initTE) of
                (Right t ,_) -> do
                    print t
                    case runEval (evalOne (last e)) of
                        (Right v, env) -> print v
                        (Left err, _) -> print err
                    
        (Left err, _) -> print err
