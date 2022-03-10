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
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

type Eval a = ExceptT Error (State Global) a

data Global
    = Global
    {
        vars :: Map Name Value
    ,   names :: Set Name
    ,   tomatch :: Maybe Value
    ,   currentname :: Maybe Name
    ,   decls :: Map Name [Expr]
    -- ,   main :: Bool -- is there a main function
    }
    deriving (Show, Eq, Ord)

fromPEGlobal :: PE -> Global -> Global
fromPEGlobal PE{..} Global{..} = Global{decls = M.map reverse declpat <> decls, ..}

initGlobal :: Global
initGlobal 
    = Global
    {
        vars = M.empty
    ,   names = S.empty
    ,   tomatch = Nothing
    ,   currentname = Nothing
    ,   decls = M.empty
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
        (Left err, _) -> putStrLn (errorBundlePretty err)
        (Right e, pe) -> 
            case runState (runExceptT (inferProgram e)) (fromPE pe initTE) of
                    (Right t ,_) -> print t
                    (Left err, _) -> print err

evalPure :: Text -> IO ()
evalPure line = do
    case exec pSource line of
        (Left err, _) -> putStrLn (errorBundlePretty err)
        (Right e, pe) -> 
            case runState (runExceptT (inferProgram e)) (fromPE pe initTE) of
                    (Right t ,te) -> print te
                    (Left err, _) -> print err

add :: Name -> Value -> Eval ()
add n v = do
    Global{..} <- get
    put Global{vars = M.insert n v vars, ..}

find :: Name -> Eval [Expr]
find name = do
    decls <- gets decls
    case M.lookup name decls of
        Nothing -> throwError (NoSuchVariable name)
        Just exs -> return exs

updated :: Name -> [Expr] -> Eval ()
updated n e = do
    Global{..} <- get
    put Global{decls = M.insertWith (<>) n e decls, ..}

emplace :: Value -> Eval ()
emplace v = do
    Global{..} <- get
    put Global{tomatch = return v, ..}

clear :: Eval ()
clear = do
    Global{..} <- get
    put Global{tomatch = Nothing, ..}

-- evalExpr :: Expr -> Eval Value
-- evalExpr e = do
--     case e of
--         App a b -> do
--             eb <- evalExpr b
--             emplace eb
--             ea <- evalExpr a
--             clear
--             return ea
--         Lam pat e -> do
--             v <- gets tomatch
--             case v of
--                 Nothing -> return (LamV mempty pat e)
--                 Just val -> do
--                     case runMatcher (match pat val) of
--                         (Right True, env) -> return (LamV env e)
--                         (Left err, _) -> throwError err
--         Var n -> find n
--         Constructor n -> return (ConV n [])
--         Let n e1 e2 -> do
--             ee1 <- evalExpr e1
--             return (LamV (M.singleton n ee1) e2)
--         Lit l -> return (LitV l)
--         If c e1 e2 -> do
--             cond <- evalExpr c
--             if cond == (ConV "True" [])
--                 then evalExpr e1
--                 else evalExpr e2

-- evalProgram :: Program -> Eval Value
-- evalProgram = undefined

-- inline :: Declaration -> Eval ()
-- inline decl = do
--     case decl of
--         Const name expr -> do
--             checkOccurence name
--             case expr of
--                 Var n -> do
--                     e <- find n
--                     updated name e

-- TODO: evaluation and inlining


-- runEval :: Eval Value -> (Either Error Value, Global)
-- runEval e = runState (runExceptT e) initGlobal

-- evio :: IO ()
-- evio = do
--     l <- getLine
--     case exec pSource (T.pack l) of
--         (Right e, pe) -> 
--             case runState (runExceptT (inferProgram e)) (fromPE pe initTE) of
--                 (Right t ,_) -> do
--                     print t
--                     case runEval (evalOne (last e)) of
--                         (Right v, env) -> print v
--                         (Left err, _) -> print err
                    
--         (Left err, _) -> print err
