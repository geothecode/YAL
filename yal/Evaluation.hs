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
import Data.List (elem)
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
    -- ,   tomatch :: Maybe Value
    ,   frompat :: [Name]
    ,   currentname :: Maybe Name
    ,   decls :: Map Name [Expr]
    -- ,   main :: Bool -- is there a main function | is it a main module
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
    -- ,   tomatch = Nothing
    ,   frompat = mempty
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

-- TODO
-- find :: Name -> Eval [Expr]
find :: Name -> Eval Expr
find name = do
    decls <- gets decls
    case M.lookup name decls of
        Nothing -> throwError (NoSuchVariable name)
        Just exs -> return (head exs) -- BAD! make an algortihm or something

updated :: Name -> [Expr] -> Eval ()
updated n e = do
    Global{..} <- get
    put Global{decls = M.insertWith (<>) n e decls, ..}

emplace :: Name -> Eval ()
emplace v = do
    Global{..} <- get
    put Global{frompat = v:frompat , ..}

clear :: Eval ()
clear = do
    Global{..} <- get
    put Global{frompat = [], ..}

evalExpr :: Expr -> Eval Value
evalExpr e = do
    case e of
        App a b -> do
            ea <- evalExpr a
            eb <- evalExpr b
            case ea of
                LamV env pat v -> do
                    if env == mempty
                        then case runMatcher (match pat eb) of
                            (Right cond, nenv) ->
                                if cond
                                    then do
                                        foldM (flip inlineValue) v (M.toList nenv)
                                    else throwError NoMatchingPatterns
                            (Left err, _) -> throwError err
                        else undefined
                ConV n xs -> return (ConV n (xs <> [eb]))
                _ -> throwError TODO
        Lam pat e -> do
            mapM emplace (freenames pat)
            ev <- evalExpr e
            clear
            return (LamV mempty pat ev)
        Var n -> do -- TODO
            ns <- gets frompat
            if n `elem` ns
                then return (VarV n)
                else do
                    ex <- find n
                    v <- evalExpr ex
                    return v
        Constructor n -> return (ConV n [])
        Let n e1 e2 -> do
            inl <- inline (n, e1) e2
            ev <- evalExpr inl
            return ev
        Lit l -> return (LitV l)
        If c e1 e2 -> do
            cond <- evalExpr c
            if cond == (ConV "True" [])
                then evalExpr e1
                else evalExpr e2
        _ -> throwError UnknownError

freenames :: Pattern -> [Name]
freenames (VariableP n) = [n]
freenames (DataConstructorP _ pats) = concat (fmap freenames pats)
freenames _ = []

inline :: (Name, Expr) -> Expr -> Eval Expr
inline (n, e1) e2 = do
    case e2 of
        Var a -> do
            if a == n
                then return e1
                else return e2
        Lam p e -> do
            inl <- inline (n, e1) e
            return (Lam p inl)
        Let a b c -> do
            inl1 <- inline (n, e1) b
            inl2 <- inline (n, e1) c
            inline (a, b) c
        App a b -> do
            inl1 <- inline (n, e1) a
            inl2 <- inline (n, e1) b
            return (App inl1 inl2)
        If a b c -> do
            inl1 <- inline (n, e1) a
            inl2 <- inline (n, e1) b
            inl3 <- inline (n, e1) c
            return (If inl1 inl2 inl3)

inlineValue :: (Name, Value) -> Value -> Eval Value
inlineValue p@(n, e1) e2 = do
    case e2 of
        l@LitV{} -> return l
        LamV env pat val -> do
            nval <- inlineValue p val
            nenv <- mapM (inlineValue p) env
            return (LamV nenv pat nval)
        ConV name vals -> do
            nvals <- mapM (inlineValue p) vals
            return (ConV name nvals)
        VarV na -> do
            if na == n
                then return e1
                else return e2 
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

evalProgram :: Eval Value
evalProgram = do
    decs <- gets decls
    case M.lookup "main" decs of
        Nothing -> throwError NoMainFunction
        Just a -> evalExpr (head a) -- TODO REDO and e t c

runEval :: PE -> Eval Value -> (Either Error Value, Global)
runEval pe e = runState (runExceptT e) (fromPEGlobal pe initGlobal)

-- evio :: IO ()
-- evio = do
--     l <- getLine
--     case exec pSource (T.pack l) of
--         (Right e, pe) -> 
--             case runState (runExceptT (inferProgram e)) (fromPE pe initTE) of
--                 (Right t ,_) -> do
--                     print t
--                     case runEval (evalExpr (last e)) of
--                         (Right v, env) -> print v
--                         (Left err, _) -> print err
                    
--         (Left err, _) -> print err


eve :: Text -> IO ()
eve l = 
    case exec (expr <|> pPragma *> expr) l of
        (Right e, pe) ->
            case runEval pe (evalExpr e) of
                (Right a, _) -> print a
                (Left err, _) -> print err
        (Left err, _) -> putStrLn (errorBundlePretty err)

evp :: Text -> IO ()
evp l = 
    case exec pSource l of
        (Right _, pe) ->
            case runEval pe evalProgram of
                (Right a, _) -> print a
                (Left err, _) -> print err
        (Left err, _) -> putStrLn (errorBundlePretty err)
{-
Summary:

i need to write right rule for inlining Variables (check TODOs)

i need to write the evaluator of declarations

-}