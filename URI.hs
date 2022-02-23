{-#
    LANGUAGE
        OverloadedStrings,
        RecordWildCards
#-}

module Parsing where

import qualified Control.Applicative as App
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Control.Monad.Trans
import Data.Functor (void)
import Text.Megaparsec.Debug

type Parser = Parsec Void Text
type Tarser = ParsecT Void Text IO

-- | Information
{- | Monads
    ParsecT e s m a
        e - custom error message
        s - input stream
        m - inner monad
        a - result of parsing

    class Stream s where
        type Token s :: *
        type Tokens s :: *
        take1_ :: s -> Maybe (Token s, s)
        tokensToChunk :: Proxy s -> [Token s] -> Tokens s
                | -}

-- | The URI Parser

-- | scheme:[//[user:password@]host[:port]][/path][?query][#fragment]

data URI = URI 
    { 
        uriScheme       :: Scheme
    ,   uriAuthority    :: Maybe Authority }
    deriving (Show, Eq)

data Scheme
    = SchemeFtp
    | SchemeIrc
    | SchemeData
    | SchemeFile
    | SchemeHttp
    | SchemeHttps
    | SchemeMailto
    deriving (Show, Eq)

data Authority = Authority
    {
        authorityUser :: Maybe (Text, Text)
    ,   authorityHost :: Text
    ,   authorityPort :: Maybe Int
    ,   authorityPath :: [Text]
    ,   authorityQuery :: Maybe Text
    ,   authorityFragment :: Maybe Int  }
    deriving (Show, Eq)

scheme :: Parser Scheme
scheme = 
        string "ftp"    $> SchemeFtp
    <|> string "irc"    $> SchemeIrc
    <|> string "data"   $> SchemeData
    <|> string "file"   $> SchemeFile
    <|> string "https"  $> SchemeHttps
    <|> string "http"   $> SchemeHttp
    <|> string "mailto" $> SchemeMailto

infixr 6 $>
a $> b = b <$ a



uri :: Parser URI
uri = do
    uriScheme <- scheme <?> "valid scheme"
    char ':'
    uriAuthority <- optional $ do
        string "//"
        authorityUser <- optional $ try $ do
            user <- T.pack <$> some alphaNumChar
            char ':'
            password <- T.pack <$> some alphaNumChar
            char '@'
            return (user, password)
        authorityHost <- T.pack <$> some (alphaNumChar <|> char '.')
        authorityPort <- optional $ char ':' *> Lexer.decimal
        authorityPath <- many $ (T.pack <$> (char '/' *> some alphaNumChar))
        authorityQuery <- optional $ T.pack <$> (char '?' *> some alphaNumChar)
        authorityFragment <- optional $ char '#' *> Lexer.decimal
        return Authority{..}
    return URI{..}

