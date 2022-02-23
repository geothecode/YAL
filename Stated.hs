{-#
    LANGUAGE
        OverloadedStrings
#-}

module Stated where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Control.Monad.State.Strict

-- | Lang33 some kinda stuff :)

data Context = Lifted | NotLifted
    deriving Show

type Parser = ParsecT Void Text (State Context)

name :: Parser Text
name = (T.pack <$> some alphaNumChar) <* (lifted <|> (string "" <* put NotLifted))
    where
        lifted = string "@" <* put Lifted
