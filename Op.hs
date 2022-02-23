{-#
    LANGUAGE
        OverloadedStrings,
        RecordWildCards,
        NamedFieldPuns
#-}
module Op where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Control.Monad.State
import Control.Monad.Combinators.Expr
import Data.Map (Map)
import qualified Data.Map as M
import Text.Megaparsec.Debug
import Text.Megaparsec (between)
import Data.List hiding (insert)

type Table = Map Int [Operator Parser Expr]
type Extensions = [Extension]
-- parsing environment
data PE = PE
    {
        btable :: Table
    ,   utable :: Table
    ,   exts :: Extensions
    ,   rec :: Bool -- used for parsing let rec expressions
    ,   lastoffset :: Int -- last errror offset
    ,   tmodule :: Maybe Declaration
    ,   warnings :: [(Int, Text)] -- TODO: change to Error from Megaparsec
    }

warn :: Text -> Parser Expr
warn text = do
    o <- getOffset
    PE{warnings, ..} <- get
    put PE{warnings = (o,text):warnings, ..}
    return (Decl $ Warning text)


type Parser = ParsecT Void Text (State PE)

spaces :: Parser ()
spaces = 
    Lexer.space
        space1
        (Lexer.skipLineComment "/*\\" <|> Lexer.skipLineComment "--")
        (Lexer.skipBlockComment "/*" "\\*")

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaces

symbol :: Text -> Parser Text
symbol = Lexer.symbol spaces

keyword :: Text -> Parser Text
keyword a = lexeme (string a <* notFollowedBy alphaNumChar)

type Name = Text

data Literal
    = Number Int
    | Boolean Bool
    | Text Text
    | Character Char
    deriving (Show, Eq, Ord)

data Expr
    = Var Name
    | App Expr Expr
    | Lam Name Expr
    | Let Name Expr Expr
    | Lit Literal
    | If Expr Expr Expr
    | Fix Expr
    | Infix Name Expr Expr
    | Postfix Name Expr
    | Prefix Name Expr
    | Pragma Pragma
    | Decl Declaration
    | Meta Expr
    deriving (Show, Eq, Ord)

data Declaration
    = Op Name I Int
    | Warning Name
    | Import [Name] [Quantifier]
    | Module [Name]
    | Const Name Expr
    deriving (Show, Eq, Ord)

data Quantifier
    = Hiding [Text]
    | Qualified Text
    | From Text -- PackageImports
    deriving (Show, Eq, Ord)

data Pragma
    = FFI Language Text -- represents ffi from <lang> in form of textual representation of source code, which can be parsed later
    | EXT [Extension] -- extension
    | OPTS Text -- compiler options
    -- e. g.
    deriving (Show, Eq, Ord)

data Language
    = Haskell
    | C
    deriving (Show, Eq, Ord)

data Extension
    = LowPrecedenceOperators
    | HighPrecedenceOperators
    | AnyPrecedenceOperators
    | LinearTypes
    | DependentTypes -- one day probably
    | LazyEvaluation -- one day probably
    | Wildcards
    | PatternMatching -- pretty small amount but
    | PostfixOperators
    | PackageImports
    | None
    deriving (Show, Eq, Ord)

infixr 6 $>
a $> b = b <$ a

data I = N | L | R | Post
    deriving (Show, Eq, Ord)

name :: Parser Text
name = lexeme (T.cons <$> lowerChar <*> (T.pack <$> many alphaNumChar))

pVar :: Parser Expr
pVar = Var <$> name

pNum :: Parser Expr
pNum = Lit <$> Number <$> lexeme Lexer.decimal

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")


-- higher = bigger precedence
initPE :: PE
initPE = PE{btable = M.fromList [], utable = {- insert (9, unary' "@") $ -} M.fromList [], exts = [], rec = False, lastoffset = 0, tmodule = Nothing, warnings = []}
{- @ is used to reference to this particular type-variable -}

-- Maybe we should return (Var a) for unification purposes ? ISSUE:
binary :: I -> Text -> Operator Parser Expr
binary N a = InfixN (Infix a <$ symbol a)
binary L a = InfixL (Infix a <$ symbol a)
binary R a = InfixR (Infix a <$ symbol a)

unary :: Text -> Operator Parser Expr
unary a = Control.Monad.Combinators.Expr.Postfix (Op.Postfix a <$ symbol a)

unary' :: Text -> Operator Parser Expr
unary' a = Control.Monad.Combinators.Expr.Prefix (Op.Prefix a <$ symbol a)

flat :: Table -> [[Operator Parser Expr]]
flat a = snd <$> M.toDescList a

insert :: (Int, Operator Parser Expr) -> Table -> Table
insert (a,b) xs = M.insertWith (<>) a [b] xs

insert' :: [(Int, Operator Parser Expr)] -> Table -> Table
insert' xs ys = foldr insert ys xs


pInfix :: Parser Expr -- change me to ()
pInfix = do
    t <- choice 
        [
            keyword "infixl" $> L
        ,   keyword "infixr" $> R
        ,   keyword "infix"  $> N
        ]
    fixity <- optional $ lexeme $ do
        o <- getOffset
        s <- optional $ char '-'
        n <- Lexer.decimal
        PE{..} <- get -- setting last error offset
        put PE{lastoffset = o, ..}
        case s of
            Just _ -> return (negate n)
            Nothing -> return n
    f <- case fixity of
            Nothing -> return 9
            Just a -> do
                o <- lastoffset <$> get
                if a > 9
                    then cIfTurnedOn HighPrecedenceOperators (return a) (do
                        setOffset o
                        fail "precedence cannot be higher than 9, maybe you meant HighPrecedenceOperators instead?") 
                    else if a < 0
                        then cIfTurnedOn LowPrecedenceOperators (return a) (do
                            setOffset o
                            fail "precedence cannot be lower than 0, maybe you meant LowPrecedenceOperators instead?")
                        else return a
    Var op <- pOp
    PE{..} <- get
    put (PE{btable = insert (f, binary t op) btable, ..})
    return (Decl $ Op op t f)

pPostfix :: Parser Expr
pPostfix = do
    t <- keyword "postfix" $> Post
    f <- return 9 -- mostly TODO:
    Var op <- pOp
    PE{..} <- get
    put (PE{utable = insert (f, unary op) utable, ..})
    return (Decl $ Op op t f)



bar :: Parser Char
bar = lexeme $ char '|' 

matchlang :: String -> Language
matchlang "haskell" = Haskell
matchlang "c" = C

pPragma :: Parser Expr
pPragma = lexeme $ curly $ do
    o <- getOffset
    name <- lexeme $ some letterChar
    case name of
        "ffi" -> do
            lang <- optional $ symbol ":" *> some letterChar
            l <- case lang of
                Nothing -> return Haskell
                Just a -> return (matchlang a)
            bar
            arg <- T.pack <$> (lexeme $ some (noneOf ("}" :: String)))
            return (Pragma $ FFI l arg)
        "opts" -> do
            fail "opts pragma will be available in futher versions of yal"
        "ext" -> do
            bar
            PE{exts = e, ..} <- get
            exts <- (e <>) <$> pExtensions `sepBy1` symbol ","
            put PE{..}
            return (Pragma $ EXT exts)
        "meta" -> do
            bar
            Meta <$> expr
        other -> do
            setOffset o
            fail ("unsupported pragma: " <> other)


curly :: Parser a -> Parser a
curly = between (symbol "{") (symbol "}")

argsTo :: Parser a -> Parser [Text]
argsTo p = choice
    [
        p $> []
    ,   (<>) <$> ((\a -> [a]) <$> name) <*> argsTo p
    ,   argsTo p
    ,   empty $> []
    ]

construct :: [Text] -> Expr -> Expr
construct xs e = foldr Lam e xs

pOp :: Parser Expr
pOp = Var <$> (T.pack <$> lexeme (some (oneOf ("+-$%&^*/?.,~@<>|#=:" :: String))))

pOp' :: Parser Text
pOp' = (T.pack <$> lexeme (some (oneOf ("+-$%&^*/?.,~@<>|#=:" :: String))))

pLam :: Parser Expr
pLam = Lam <$> 
        ((keyword "lam" <|> symbol "\\") *> name) -- lam x OR \x
    <*> ((construct <$> argsTo (symbol "->")) >>= (\a -> a <$> expr)) -- zero or some other args and -> followed by expr

pExtensions :: Parser Extension
pExtensions = choice
    [
        symbol "PatternMatching" $> PatternMatching
    ,   (symbol "LowPrecedenceOperators" <|> symbol "LPO") $> LowPrecedenceOperators
    ,   (symbol "HighPrecedenceOperators" <|> symbol "HPO") $> HighPrecedenceOperators
    ,   symbol "PostfixOperators" $> PostfixOperators
    ,   symbol "PackageImports" $> PackageImports
    ,   do
            o <- getOffset
            n <- some letterChar
            setOffset o
            fail ("no such an extension: " <> n)
    ]   <?> "extension"

pLet :: Parser Expr
pLet = Let <$> (keyword "let" *> name) <*> (((construct <$> argsTo (symbol "=")) >>= (\a -> a <$> expr)) <|> (symbol "=" *> expr)) <*> (keyword "in" *> expr)

-- TODO: pattern matching and stuff combinators
-- "c" in name for COMBINATOR

cIfTurnedOn :: Extension -> Parser a -> Parser a -> Parser a
cIfTurnedOn ext a b = do
    es <- exts <$> get
    if ext `elem` es
        then a
        else b

pApp :: Parser Expr
pApp = (\a b -> foldl App a b) <$> term <*> some term <* notFollowedBy (keyword "=")


pName :: Parser Text
pName = lexeme (T.cons <$> (upperChar <|> lowerChar) <*> (T.pack <$> many alphaNumChar))

pImport :: Parser Expr
pImport = lexeme $ do
    keyword "import"
    n <- lexeme (pName `sepBy1` symbol ".") <?> "package name"
    qual <- optional $ do
        keyword "as"
        asn <- pName
        return (Qualified asn)
    fr <- cIfTurnedOn PackageImports (optional $ do
        keyword "from"
        frn <- (pName <|> name)
        return (From frn)
        ) (return Nothing)
    hid <- optional $ do
        keyword "hiding"
        let names = pName <|> name
        ns <- (return <$> (names <|> parens pOp')) <|> parens (((names <|> parens pOp') `sepBy1` symbol ",") <?> "things to hide")
        o <- getOffset
        notFollowedBy (symbol ",") <|> do
            setOffset o
            fail "Unexpected ',': maybe you meant to use parenthesis instead?"
        return (Hiding ns)
    return (Decl $ Import n $ concat $ map fromMaybe [qual, fr, hid])
    -- TODO:

pModule :: Parser Expr
pModule = do
    PE{tmodule,..} <- get
    case tmodule of
        Nothing -> do
            keyword "module"
            mod <- Module <$> lexeme (pName `sepBy1` symbol ".") <?> "module name"
            PE{..} <- get
            put PE{tmodule = Just mod, ..}
            return (Decl mod)
        Just a -> do
            fail "module had been already declared"



fromMaybe :: (Maybe a) -> [a]
fromMaybe Nothing = []
fromMaybe (Just a) = [a]

term :: Parser Expr
term =
    choice
        [
            parens pOp
        ,   parens expr
        -- ,   cIfTurnedOn PatternMatching pPLam pLam -- for example
        ,   pLam
        ,   pLet
        ,   pVar
        ,   pNum
        ]

top :: Parser Expr
top = 
    choice
        [
            pModule
        ,   pImport
        ,   pInfix
        ,   cIfTurnedOn PostfixOperators pPostfix empty
        ,   pPragma
        ]
{-
    choice
        [
            dbg "parens" $ parens expr
        ,   dbg "infix" $ infixP
        ,   dbg "var" var
        ,   dbg "num" num
        ]
-}

expr :: Parser Expr
expr = do
    e <- get
    makeExprParser (top <|> try (parens pApp <|> pApp) <|> pDecl <|> term) (flat $ utable e <> btable e) -- WORKS!!!!!

test :: Show a => Parser a -> Text -> IO ()
test p t = case evalState (runParserT p "<input>" t) initPE of
    Right x -> print x
    Left e -> putStrLn $ errorBundlePretty e

-- Top-Level Parsers

pDecl :: Parser Expr
pDecl = Decl <$> (Const <$> name <*> (((construct <$> argsTo (symbol "=")) >>= (\a -> a <$> expr)) <|> (symbol "=" *> expr)))

-- pTypeSig :: Parser Expr -- TODO: type level operators and makeExprParser for them (maybe use state?)
-- pTypeSig = name <*> 
