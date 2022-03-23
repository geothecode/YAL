module Shell where

import Module
import Pretty
import Syntax
import Parsing
import Evaluation
import Typing

import Data.Map (Map)
import Data.Map as M
import Control.Monad.State
-- import Control.Monad.Except
import Data.Text (Text)
import Data.List (elem)
import qualified Data.Text as T
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import System.Directory
import System.IO
import System.IO.Unsafe
import qualified System.Process as PROC

data    ShellBuffer
    =   ShellBuffer
    {
        penv :: PE
    ,   tenv :: TE
    ,   glob :: Global
    ,   file :: FilePath
    ,   exns :: [Extension]
    }

type Shell = StateT ShellBuffer IO

instance Semigroup ShellBuffer where
    (<>) = adjustShell

instance Monoid ShellBuffer where
    mempty = ShellBuffer
        {
            penv = mempty
        ,   glob = mempty
        ,   tenv = mempty
        ,   file = "input"
        ,   exns = mempty
        }

adjustShell :: ShellBuffer -> ShellBuffer -> ShellBuffer
adjustShell s1 s2 = s2 {penv = (penv s1) <> (penv s2), glob = (glob s1) <> (glob s2), tenv = (tenv s1) <> (tenv s2)}

shellStepParser :: Parser (Either Expr [Declaration])
shellStepParser = (Right <$> (pSource <?> "declaration") <|> Left <$> (expr <?> "expression to evaluate"))

argParser :: Parser (Either Text Expr)
argParser = (Right <$> (parens expr <?> "specified sxpression") <|> Left <$> (name <?> "argument"))

commandParser :: Parser (Command, Maybe (Either Text Expr))
commandParser = do
            symbol ":"
            com <- some (alphaNumChar <|> oneOf (T.unpack "!*^%$#&@?"))
            sc
            arg <- optional $ argParser
            let c = case com of
                        a | (a `elem` ["l", "load"]) -> LoadFile
                        a | (a `elem` ["r", "reload"]) -> ReloadFile
                        a | (a `elem` ["t", "type"]) -> WhichType
                        a | (a `elem` ["q", "quit"]) -> QuitSession
                        a | (a `elem` ["c", "clear"]) -> ClearConsole
                        a | (a `elem` ["pe"]) -> PrintEnv
                        a | (a `elem` ["!"]) -> CallCommand
            return (c, arg)

evalCommand :: (Command, Maybe (Either Text Expr)) -> ShellBuffer -> IO ()
evalCommand (c,a) sb = case c of
    QuitSession -> putStrLn "finishing session..."
    ClearConsole -> PROC.callCommand "cls" >> shell sb
    LoadFile -> case a of
        Just (Left fname) -> undefined
        _ -> shell sb
    CallCommand -> case a of
        Just (Left cmd) -> PROC.callCommand (T.unpack cmd) >> shell sb
        _ -> shell sb
    WhichType -> case a of
        (Just (Left name)) -> undefined

upgl :: Global -> ShellBuffer -> ShellBuffer
upgl g b = b {glob = g <> (glob b)}

uppe :: PE -> ShellBuffer -> ShellBuffer
uppe pe b = b {penv = pe <> (penv b)}


shell :: ShellBuffer -> IO ()
shell b = do
    -- line <- liftIO $ shellGetLine
    putStr "sh> "
    line <- (\a -> if a == "" then ":!" else T.pack a) <$> getLine
    case execute commandParser line mempty (file b) of
        (Right c, _) -> evalCommand c b
        _ -> do
            case execute shellStepParser line (penv b) (file b) of
                (Right parsed, pe) -> do
                    let b' = (upgl (fromPE pe (glob b)) $ uppe pe b)
                    case parsed of
                        Left expr -> do
                            v <- runEval (glob b') (evalExpr expr mempty)
                            putStrLn $ 
                                case v of
                                    (Left err, _) -> runPretty err
                                    (Right value, _) -> runPretty value
                            shell b'
                        Right decl -> do
                            v <- runEval (glob b') (mapM fromDecl decl)
                            case v of
                                (_, gl) -> do
                                    shell (upgl gl b')
                (Left err, _) -> do
                    putStrLn (errorBundlePretty err)
                    shell b
-- shell :: ShellBuffer -> IO ()
-- shell b = do
--     -- line <- liftIO $ shellGetLine
--     putStr "sh> "
--     line' <- getLine
--     let line = T.pack line'
--     case line' of
--         (':':'q':_) -> putStrLn "finishing session..."
--         _ -> do
--             case exec shellStepParser line of
--                 (Right parsed, pe) -> do
--                     let b' = uppe pe b
--                     case parsed of
--                         Left expr -> do
--                             v <- runEval (glob b') (evalExpr expr mempty)
--                             putStrLn $ 
--                                 case v of
--                                     (Left err, _) -> runPretty err
--                                     (Right value, _) -> runPretty value
--                             shell b'
--                         Right decl -> do
--                             v <- runEval (glob b') (mapM fromDecl decl)
--                             case v of
--                                 (_, gl) -> do
--                                     shell (upgl gl b')
--                 (Left err, _) -> do
--                     putStrLn (errorBundlePretty err)
--                     shell b
-- shellGetLine :: IO Text
-- shellGetLine = T.pack <$> do
--     line <- getLine
--     case line of