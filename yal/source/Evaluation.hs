{-#
    LANGUAGE
        OverloadedStrings
#-}

module Evaluation where

import Parsing
import Typing hiding (locl)
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
    ,   locl :: Map Name Value
    ,   locle :: Map Name Expr
    ,   out :: [Value]
    -- ,   main :: Bool -- is there a main function | is it a main module
    }
    deriving (Show, Eq, Ord)

fromPEGlobal :: PE -> Global -> Global
fromPEGlobal pe g = g {decls = M.map reverse (declpat pe) <> decls g}

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
    ,   locl = M.empty
    ,   locle = M.empty
    ,   out = mempty
    }

checkOccurence :: Name -> Eval ()
checkOccurence name = do
    g <- get
    if name `S.member` names g
        then throwError (MultipleDeclaration name)
        else put (g {names = name `S.insert` names g})

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
    g <- get
    put (g {vars = M.insert n v (vars g)})

makeAlt :: Expr -> Alt
makeAlt (Lam p e) = (p, e)
-- makeAlt x = Left x

makeCase :: [Expr] -> Expr
makeCase xs = let 
    var = (VariableP "0") in
        Lam var (Case (Var "0") (fmap makeAlt xs))

-- TODO
-- find :: Name -> Eval [Expr]
find :: Name -> Env -> Eval Value
find name en = do
    decls <- gets decls
    loc <- gets locl
    case M.lookup name en of
        Just v -> return v
        Nothing -> case M.lookup name decls of
            Nothing -> case M.lookup name loc of
                Nothing -> throwError (NoSuchVariable name)
                Just v -> return v
            Just exs -> evalExpr (makeCase exs) en -- BAD! make an algortihm or something

updated :: Name -> [Expr] -> Eval ()
updated n e = do
    g <- get
    put (g {decls = M.insertWith (<>) n e (decls g)})

-- emplace :: Name -> Eval ()
-- emplace v = do
--     g <- get
--     put (g {frompat = v:(frompat g)})

-- clear :: Eval ()
-- clear = do
--     g <- get
--     put (g {frompat = []})

outAdd :: Value -> Global -> Eval ()
outAdd v g = do
    put (g {out = out g <> return v})

-- | a bit of Pretty
showValue :: Value -> Text
showValue v = T.pack $ case v of
    LitV (Number a) -> show a
    LitV (Character a) -> show a
    (ConV "TextCons" (x:xs)) -> "\"" <> show x <> show xs <> "\""
    (ConV "TextNil" _) -> ""
    (ConV a _) -> T.unpack a

-- | Main things

evalExpr :: Expr -> Env -> Eval Value
evalExpr e en = do
    case e of
        -- Var "getln" -> return Input
        App a b -> do
            case a of
                Var "print" -> do
                    eb <- evalExpr b mempty
                    g <- get
                    outAdd eb g
                    return (ConV "IO" [])
                Var "show" -> do
                    eb <- evalExpr b mempty
                    return (LitV (Text (showValue eb)))
                _ -> do
                    ea <- evalExpr a mempty
                    eb <- evalExpr b mempty
                    case ea of
                        LamV env pat e -> do
                                case runMatcher (match pat eb) of
                                    (Right cond, nenv) ->
                                        if cond
                                            then do
                                                v <- evalExpr e (env <> nenv)
                                                return v
                                                -- foldM (flip inlineValue) v (M.toList nenv)
                                            else throwError NoMatchingPatterns
                                    (Left err, _) -> throwError err
                        ConV n xs -> return (ConV n (xs <> [eb]))
                        _ -> throwError TODO
        Case e alts -> firstin e en alts
        Infix op l r -> do
            l' <- evalExpr l mempty
            r' <- evalExpr r mempty
            return (evalBinary (fromOp op) l' r')
        Lam pat e -> case pat of
            -- EmptyP -> evalExpr e en
            _ -> return (LamV en pat e)
        Var n -> find n en
        Constructor n -> return (ConV n [])
        Let n e1 e2 -> do
            e <- evalExpr e1 mempty
            ev <- evalExpr e2 (M.singleton n e)
            return ev
        Lit l -> return (LitV l)
        If c e1 e2 -> do
            cond <- evalExpr c mempty
            if cond == (ConV "True" [])
                then evalExpr e1 mempty
                else evalExpr e2 mempty
        _ -> throwError UnknownError

firstin :: Expr -> Env -> [Alt] -> Eval Value
firstin _ _ [] = throwError NotCompletePatterns
firstin e env ((p,exp):xs) = do
    val <- evalExpr e env
    case runMatcher (match p val) of
        (Right cond, nenv) -> do
            let n = env <> nenv
            if cond
                then do
                    v <- evalExpr exp n
                    return v
                else firstin e n xs
        (Left err, _) -> throwError err

-- sayExprs :: Map Name Expr -> Eval ()
-- sayExprs m = do
--     g <- get
--     put (g {locle = locle g <> m})

-- clearExprs :: Eval ()
-- clearExprs = do
--     g <- get
--     put (g {locle = mempty})

-- sayVal :: Name -> Value -> Eval ()
-- sayVal n v = do
--     g <- get
--     put (g {locl = M.insert n v (locl g)})

-- sayVals :: Map Name Value -> Eval ()
-- sayVals m = do
--     g <- get
--     put (g {locl = locl g <> m})

-- clearVal :: Name -> Eval ()
-- clearVal n = do
--     g <- get
--     put (g {locl = M.delete n (locl g)})

fromOp :: Name -> (Value -> Value -> Value)
fromOp "+" = plusl
fromOp "-" = minusl
fromOp "*" = multl
fromOp "/" = divl
fromOp ">" = gtl
fromOp "<" = ltl
fromOp "==" = eql

evalBinary :: (Value -> Value -> Value) -> Value -> Value -> Value
evalBinary f a b = (f a b)

plusl (LitV (Number a)) (LitV (Number b)) = LitV (Number (a + b))
minusl (LitV (Number a)) (LitV (Number b)) = LitV (Number (a - b))
multl (LitV (Number a)) (LitV (Number b)) = LitV (Number (a * b))
divl (LitV (Number a)) (LitV (Number b)) = LitV (Number (a `div` b))
gtl a b = (ConV (T.pack $ show (a > b)) [])
ltl a b = (ConV (T.pack $ show (a < b)) [])
eql a b = (ConV (T.pack $ show (a == b)) [])

freenames :: Pattern -> [Name]
freenames (VariableP n) = [n]
freenames (DataConstructorP _ pats) = concat (fmap freenames pats)
freenames _ = []


-- deprecated
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

-- inlineValue :: (Name, Value) -> Value -> Eval Value
-- inlineValue p@(n, e1) e2 = do
--     case e2 of
--         l@LitV{} -> return l
--         LamV env pat val -> do
--             nval <- inlineValue p val
--             nenv <- mapM (inlineValue p) env
--             return (LamV nenv pat nval)
--         ConV name vals -> do
--             nvals <- mapM (inlineValue p) vals
--             return (ConV name nvals)
        -- VarV na -> do
        --     if na == n
        --         then return e1
        --         else return e2 
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
        Just a -> evalExpr (head a) mempty -- TODO REDO and e t c

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
            case runEval pe (evalExpr e mempty) of
                (Right a, _) -> print a
                (Left err, _) -> print err
        (Left err, _) -> putStrLn (errorBundlePretty err)

evp :: Text -> IO ()
evp l = 
    case exec pSource l of
        (Right ast, pe) ->
            
                    case runEval pe evalProgram of
                        (Right a, _) -> print a
                        (Left err, _) -> print err
        (Left err, _) -> putStrLn (errorBundlePretty err)

typeOf :: Text -> IO ()
typeOf l = do
    case exec decl l of
        (Right ast, pe) ->
            case runState (runExceptT (inferDecl ast >>= generalize . snd)) (fromPE pe initTE) of
                (Left err, _) -> print err
                (Right t, te) -> print t
        (Left err, _) -> putStrLn (errorBundlePretty err)
{-
Summary:

i need to write right rule for inlining Variables (check TODOs)

i need to write the evaluator of declarations

i need to add the typechecker utility to evaluation

-}

-- evaluate :: Text -> 