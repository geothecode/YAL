module Evaluation where

import Parsing
import Typing

import Text.Megaparsec
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Text as T

evalIO :: IO ()
evalIO = do
    line@(l:ls) <- getLine
    case exec (some expr) (T.pack line) of
        (Right e, pe) -> 
            case runState (runExceptT (inferMany e)) (fromPE pe initTE) of
                (Right t ,_) -> print t

eval :: T.Text -> IO ()
eval t = case exec (some expr) t of
        (Right e, pe) -> 
            case runState (runExceptT (inferMany e)) (fromPE pe initTE) of
                (Right t ,_) -> print t
                (Left e, _) -> print e