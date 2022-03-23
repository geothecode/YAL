{-#
    LANGUAGE
        OverloadedStrings
#-}

module Evaluation where

import Parsing
-- import Typing hiding (locl)
import Syntax
import PatternMatching
import Module
import Pretty

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

type Eval a = ExceptT Error (StateT Global IO) a

data    Global
    =   Global
    {
        counter     :: Int
    ,   arity       :: Map Name Int
    ,   decls       :: Map Name Expr
    ,   isMain      :: Bool
    } deriving (Show, Eq, Ord)

instance Semigroup Global where
    (<>) = adjustGlobal

instance Monoid Global where
    mempty = Global
        {
            counter = 0
            -- utility thing
        ,   arity = mempty
            -- arity of data constructors and constants
        ,   decls = mempty
            -- declarations represented as multi-case
        ,   isMain = True
            -- set if we are in main module
        }

-- | Declarations

nullCounter :: Eval ()
nullCounter = modify (\g -> g {counter = 0})

newName :: Eval Text
newName = do
    g <- get
    put (g {counter = (counter g) + 1})
    return (T.pack . show $ counter g)

fromDecl :: Declaration -> Eval ()
fromDecl (Const name alt@(pat, cond, exp)) = do
    g <- get
    case M.lookup name (arity g) of
        Nothing -> put (g {arity = M.insert name (length pat) (arity g)})
        Just ar -> do
            if ar == length pat
                then return ()
                else throwError DifferentAmountOfArgs
    case M.lookup name (decls g) of
        Nothing -> do
            cse <- mkCase alt
            put (g {decls = M.insert name cse (decls g)})
        Just _ -> put (g {decls = (M.adjust (addAlt alt) name (decls g))})
fromDecl (Module dir) = case dir of
    ["main"] -> return ()
    [] -> return ()
    _ -> modify (\g -> g {isMain = False})
-- fromDecl (Import dir _) = case dir of
--     x -> do
--         f <- liftIO $ do
--                 p <- runFinder (findModule (last x))
--                 return (fst p)
--         case f of
--             Right source -> case exec pSource source of
--                 (Right prog, pe) -> do
--                     modify (\g -> fromPE pe g)
--                     res <- liftIO (runEval mempty (mapM fromDecl prog))
--                     case res of
--                         (Right _, global) -> modify (adjustGlobal global)
--                         (Left _, _) -> return ()
--                 -- (Left err, _) -> throwError err -- actually cannot happen (i guess)
--             Left err -> throwError err
fromDecl _ = return ()

fromPE :: PE -> Global -> Global
fromPE pe gl = gl {arity = (M.map fst (datainfo pe)) <> (arity gl)}

adjustGlobal :: Global -> Global -> Global
adjustGlobal g1 g2 = g2 {decls = (decls g1) <> (decls g2), arity = (arity g1) <> (arity g2)}

mkCase :: Alt -> Eval Expr
mkCase alt@(pat, cond, exp) = do
    ns <- mapM uniqNames pat
    nullCounter
    return (foldr (Lam . VarP) (cse ns) ns)
    where
        uniqNames _ = newName
        vars a = fmap Var a
        cse a = Case (vars a) [alt]

addAlt :: Alt -> Expr -> Expr
addAlt alt (Lam a e) = Lam a (addAlt alt e) 
addAlt alt (Case a b) = Case a (b <> [alt])

matchArity :: Name -> [Value] -> Eval [Value]
matchArity name xs = do
    a <- gets arity
    case M.lookup name a of
        Nothing -> throwError (NoSuchVariable name)
        Just ar -> if ar >= length xs
            then return xs
            else throwError DifferentAmountOfArgs

mkText :: String -> Value
mkText [] = (ConV "TextNil" [])
mkText (x:xs) = (ConV "TextCons" [LitV (Character x), mkText xs])

mkNum :: Integer -> Eval Value
mkNum = return . LitV . Number

mkBool :: Bool -> Eval Value
mkBool a = return $ ConV (T.pack $ show a) []

toText' :: String -> String
toText' xs = init (tail xs)

fromOperator :: Name -> Value -> Value -> Eval Value
fromOperator op (LitV (Number a')) (LitV (Number b')) = case op of
    "+" -> mkNum (a + b)
    "-" -> mkNum (a - b)
    "*" -> mkNum (a * b)
    "/" -> mkNum (a `div` b)
    "^" -> mkNum (a ^ b)
    ">" -> mkBool (a > b)
    "<" -> mkBool (a < b)
    "==" -> mkBool (a == b)
    ">=" -> mkBool (a >= b)
    "<=" -> mkBool (a <= b)
    "/=" -> mkBool (a /= b)
    _ -> throwError (NoSuchVariable op)
    where
        a = fromIntegral a'
        b = fromIntegral b'
fromOperator op l@(ConV "TextCons" _) r@(ConV "TextCons" _) = case op of
    "++" -> return $ mkText $ showValue l ++ showValue r
    _ -> throwError (NoSuchVariable op)

-- | Main Evaluation

evalManyE :: [Expr] -> Env -> Eval [Value]
evalManyE ex en = mapM (flip evalExpr en) ex

evalExpr :: Expr -> Env -> Eval Value
evalExpr e en = do
    case e of
        
        -- | Primitive
        Var "getln" -> do
            ex <- toText <$> liftIO getLine
            evalExpr ex mempty
        Var "undefined" -> throwError Undefined
        
        Con n -> do
            args <- matchArity n []
            return (ConV n args)
        Lit l -> return (LitV l)
        
        Infix op le re -> do
            d <- gets decls
            case M.lookup op d of
                Just _ -> evalExpr (App (App (Var op) le) re) en
                Nothing -> do
                    l <- evalExpr le en
                    r <- evalExpr re en
                    fromOperator op l r
        
        Let (Const name alt) exp -> do
            e <- mkCase alt
            v <- evalExpr e en
            evalExpr exp (M.singleton name v <> en)

        -- | Hard
        App a b -> do
            case a of
                Var "print" -> do
                    eb <- evalExpr b en
                    liftIO $ putStrLn (showValue eb)
                    return (ConV "IO" [])
                Var "read" -> do
                    eb <- evalExpr b en
                    -- let num = read (toText' (runPretty eb))
                    let num = read (runPretty eb)
                    return (LitV (Number num))
                Con "TODO" -> do
                    msg <- evalExpr b en
                    throwError (TODO (T.pack $ showText msg))
                _ -> do
                    ea <- evalExpr a en
                    eb <- evalExpr b en
                    case ea of
                        ConV n xs -> do
                            args <- matchArity n (xs <> [eb])
                            return (ConV n args)
                        LamV env pat e -> do
                            case runMatcher (match pat eb) of
                                (Right matches, nenv) ->
                                    if matches
                                        then evalExpr e (nenv <> env)
                                        else throwError NoMatchingPatterns
                                (Left err, _) -> throwError err
                        _ -> throwError CannotCallUncallable
            -- todo
                -- recursion
        If c l r -> do
            cond <- evalExpr c en
            if cond == (ConV "True" [])
                then evalExpr l en
                else evalExpr r en

        Fix v -> evalExpr (App v (Fix v)) en

        Lam pat e -> return (LamV en pat e)

        Var n -> do
            case M.lookup n en of
                Just v -> return v
                Nothing -> do
                    d <- gets decls
                    case M.lookup n d of
                        Nothing -> throwError (NoSuchVariable n)
                        Just ex -> evalExpr ex en
        
        Case exps alts -> do
            case exps of
                [] -> go alts
                x  -> do
                    vals <- evalManyE exps en
                    goMany alts vals
                where
                    go [] = throwError NoMatchingPatterns
                    go (a:as) = case a of
                        ([],Nothing, e) -> evalExpr e en
                        ([],Just cond, e) -> do
                            c <- evalExpr cond en
                            if c == (ConV "True" [])
                                then evalExpr e en
                                else go as -- todo
                    goMany [] _ = throwError NoMatchingPatterns
                    goMany (a:as) b = case a of
                        (pat,cond,e) -> do
                            case runMatcher (matchMany pat b) of
                                (Right matches, nenv) ->
                                    if matches
                                    then case cond of
                                        Nothing -> evalExpr e (nenv <> en)
                                        Just c -> do
                                            passes <- evalExpr c (nenv <> en)
                                            if passes == (ConV "True" [])
                                                then evalExpr e (nenv <> en)
                                                else goMany as b
                                    else goMany as b
                                (Left err, _) -> throwError err
                    -- redudant, todo: unify patterns above

evalSource :: [Declaration] -> Eval Value
evalSource declars = do
    mapM fromDecl declars
    cond <- gets isMain
    if cond
        then do
            d <- gets decls
            case M.lookup "main" d of
                Nothing -> throwError NoMainFunction
                Just expr -> evalExpr expr mempty
        else throwError NotInMainModule

-- | Utility Functions

toText :: String -> Expr
toText [] = Con "TextNil"
toText (x:xs) = App (App (Con "TextCons") (Lit (Character x))) (toText xs)

showValue :: Value -> String
showValue v = case v of
    LitV (Number a) -> show a
    LitV (Character a) -> show a
    t -> showText t
    -- (ConV a _) -> T.unpack a

showText :: Value -> String
showText (ConV "TextNil" []) = ""
showText (ConV "TextCons" ((LitV (Character ch)):[tc])) = "\"" <> [ch] <> go tc <> "\""
    where
        go (ConV "TextCons" ((LitV (Character ch)):[tc'])) = [ch]<>(go tc')
        go (ConV "TextNil" []) = ""

testEval :: Text -> IO ()
testEval t = case exec (some decl `sepEndBy` symbol ";" *> expr <|> expr) t of
    (Right ast, _) -> do
        res <- runEval mempty (evalExpr ast mempty)
        print res
    (Left err, _) -> putStrLn (errorBundlePretty err)

testSource :: Text -> IO ()
testSource f = case exec pSource f of
    (Right x, pe) -> do
        (v, v') <- runEval (fromPE pe mempty) (evalSource x)
        putStrLn (runPretty v)
    (Left err, _) -> putStrLn (errorBundlePretty err)

runEval :: Global -> Eval a -> IO (Either Error a, Global)
runEval g e = runStateT (runExceptT e) g