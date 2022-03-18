{-#
    LANGUAGE
        OverloadedStrings
#-}

module Evaluation where

import Parsing
-- import Typing hiding (locl)
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

type Eval a = ExceptT Error (StateT Global IO) a

data    Global
    =   Global
    {
        counter :: Int
    ,   arity :: Map Name Int
    ,   decls :: Map Name Expr
    } deriving (Show, Eq, Ord)

instance Semigroup Global where

instance Monoid Global where
    mempty = Global
        {
            counter = 0
        ,   arity = mempty
        ,   decls = mempty
        }

-- | Declarations

nullCounter :: Eval ()
nullCounter = do
    g <- get
    put (g {counter = 0})

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

-- | Main Evaluation

evalExpr :: Expr -> Env -> Eval Value
evalExpr e en = do
    case e of
        
        -- | Primitive
        Var "getln" -> do
            ex <- toText <$> liftIO getLine
            evalExpr ex mempty
        Con n -> return (ConV n [])
        Lit l -> return (LitV l)
        
        -- | Hard
        App a b -> do
            case a of
                Var "print" -> do
                    eb <- evalExpr b en
                    liftIO $ putStrLn (showValue eb)
                    return (ConV "IO" [])
                _ -> do
                    ea <- evalExpr a en
                    eb <- evalExpr b en
                    case ea of
                        ConV n xs -> return (ConV n (xs <> [eb]))
            -- todo
        
        Var n -> do
            case M.lookup n en of
                Just v -> return v
                Nothing -> do
                    d <- gets decls
                    case M.lookup n d of
                        Nothing -> throwError (NoSuchVariable n)
                        Just ex -> evalExpr ex en
        
        Case exps alts -> undefined
-- | Utility Functions

toText :: String -> Expr
toText [] = Con "TextNil"
toText (x:xs) = App (App (Con "TextCons") (Lit (Character x))) (toText xs)

showValue :: Value -> String
showValue v = case v of
    LitV (Number a) -> show a
    LitV (Character a) -> show a
    (ConV "TextCons" (x:xs)) -> "\"" <> show x <> show xs <> "\""
    (ConV "TextNil" _) -> ""
    (ConV a _) -> T.unpack a 

runEval :: Global -> Eval a -> IO (Either Error a, Global)
runEval g e = runStateT (runExceptT e) g