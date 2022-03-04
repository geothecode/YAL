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

import Text.Megaparsec hiding (State, match)
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M

evalIO :: IO ()
evalIO = do
    line@(l:ls) <- getLine
    case exec pSource (T.pack line) of
        (Right e, pe) -> 
            case runState (runExceptT (inferProgram e)) (fromPE pe initTE) of
                (Right t ,_) -> print t

eval :: T.Text -> IO ()
eval t = case exec pSource t of
        (Right e, pe) -> 
            case runState (runExceptT (inferProgram e)) (fromPE pe initTE) of
                (Right t ,_) -> print t
                (Left e, _) -> print e

data EE
    = EE
    {

    }
    deriving (Show, Eq, Ord)

