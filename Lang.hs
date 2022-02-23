{-#
    LANGUAGE
        OverloadedStrings
#-}
module Lang where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Control.Monad.Combinators.Expr

type Parser = Parsec Void Text

infixr 6 $>
a $> b = b <$ a

namingChar :: String
namingChar = "_'"

spaces :: Parser ()
spaces = 
    Lexer.space
        space1
        (Lexer.skipLineComment "/*\\")
        (Lexer.skipBlockComment "/*" "\\*")

charLiteral :: Parser Literal
charLiteral = Character <$> between (char '\'') (char '\'') Lexer.charLiteral 

textLiteral :: Parser Literal
textLiteral = Text <$> T.pack <$> ((char '\"') *> manyTill Lexer.charLiteral (char '\"'))

keyword :: Text -> Parser Text
keyword kw = string kw <* notFollowedBy (alphaNumChar <|> oneOf namingChar)

data Literal
    = Number Integer
    | Character Char
    | Text Text
    deriving (Show, Eq)

data Expr
    = Var Text
    | App Expr Expr
    | Lam Text Expr
    | Let Text Expr Expr
    | Lit Literal
    | If Expr Expr Expr
    | Fix Expr
    | Brack Expr
    | Infix Text Expr Expr
    deriving (Show, Eq)

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaces

var :: Parser Expr
var = Var <$> name <?> "variable"

lit :: Parser Expr
lit = Lit <$> choice
    [
        number
    ,   charLiteral
    ,   textLiteral ] <?> "literal"

number :: Parser Literal
number = Number <$> (lexeme $ Lexer.decimal)

name :: Parser Text
name = (\c cs -> T.cons c (T.pack cs)) <$> lowerChar <*> many alphaNumChar <?> "name"

expr :: Parser Expr
expr = choice
    [
        try $ App <$> expr <*> expr
    ,   try $ Let <$> (keyword "let" *> name) <*> expr <*> expr
    ,   lit
    ]