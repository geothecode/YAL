{-#
    LANGUAGE
        OverloadedStrings,
        RecordWildCards,
        NamedFieldPuns,
        PatternSynonyms
#-}
module Parsing where

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
import Data.Set (Set)
import qualified Data.Set as S

import Syntax

type Table a = Map Int [Operator Parser a]
-- parsing environment
data PE = PE
    {
        btable      :: Table Expr
    ,   utable      :: Table Expr
    ,   typetable   :: Table Type
    ,   exts        :: Extensions
    ,   rec         :: Bool -- used for parsing let rec expressions
    ,   lastoffset  :: Int -- last errror offset
    ,   tmodule     :: Maybe Declaration
    ,   warnings    :: [(Int, Text)] -- TODO: change to Error from Megaparsec
    ,   dtypes      :: Map Name Scheme
    ,   ddata       :: [Declaration] -- since we dont have data args yet we just collect this references
    }

warn :: Text -> Parser Expr
warn text = do
    o <- getOffset
    PE{warnings, ..} <- get
    put PE{warnings = (o,text):warnings, ..}
    return (Decl $ Warning text)

turnOn :: Extension -> Parser ()
turnOn e = do
    PE{exts, ..} <- get
    put (PE{exts = S.insert e exts, ..})

turnOff :: Extension -> Parser ()
turnOff e = do
    PE{exts, ..} <- get
    put (PE{exts = S.delete e exts, ..})

type Parser = ParsecT Void Text (State PE)

spaces :: Parser ()
spaces = 
    Lexer.space
        space1
        pLineComment
        pBlockComment

pLineComment :: Parser ()
pLineComment = 
        Lexer.skipLineComment "--"
    -- <|> Lexer.skipLineComment "/*\\"

pBlockComment :: Parser ()
pBlockComment = 
        Lexer.skipBlockComment "##" "##"
        -- Lexer.skipBlockComment "{-" "-}" 

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaces

symbol :: Text -> Parser Text
symbol = Lexer.symbol spaces

keyword :: Text -> Parser Text
keyword a = lexeme (string a <* notFollowedBy alphaNumChar)

kwrds :: [Text]
kwrds = 
    [
        "let"
    ,   "if"
    ,   "then"
    ,   "else"
    ,   "lam"
    ,   "\\"
    ,   "forall"
    ,   "rec"
    ,   "fix"
    ,   "in"
    ,   "where"
    ,   "data"
    -- ,   "exists"
    ]

name :: Parser Text
name = do
    nm <- lexeme (T.cons <$> lowerChar <*> (T.pack <$> many alphaNumChar))
    if nm `elem` kwrds
        then empty
        else return nm

pVar :: Parser Expr
pVar = Var <$> name

pNum :: Parser Expr
pNum = Lit <$> Number <$> (lexeme $ do 
    n <- optional $ char '-'
    num <- Lexer.decimal
    return $ case n of
        Just _ -> negate num
        Nothing -> num)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")


-- higher = bigger precedence
initPE :: PE
initPE = PE
    {
        btable      = insert (7, InfixL (try (ticks (name <|> try (parens name) <|> parens pOp') >>= (\a -> return (Infix a))))) M.empty
    ,   utable      = M.empty {- insert (9, unary' "@") $ -}
    ,   typetable   = insert (-1, InfixR (TypeArrow <$ symbol "->")) M.empty
    ,   exts        = S.empty
    ,   rec         = False
    ,   lastoffset  = 0
    ,   tmodule     = Nothing
    ,   warnings    = mempty
    ,   dtypes      = M.empty
    ,   ddata       = mempty
    }
{- @ is used to reference to this particular type-variable -}

-- Maybe we should return (Var a) for unification purposes ? ISSUE:
binary :: I -> Text -> Operator Parser Expr
binary N a = InfixN (Infix a <$ symbol a)
binary L a = InfixL (Infix a <$ symbol a)
binary R a = InfixR (Infix a <$ symbol a)

unary :: Text -> Operator Parser Expr
unary a = Control.Monad.Combinators.Expr.Postfix (Syntax.Postfix a <$ symbol a)

unary' :: Text -> Operator Parser Expr
unary' a = Control.Monad.Combinators.Expr.Prefix (Syntax.Prefix a <$ symbol a)

flat :: Table a -> [[Operator Parser a]]
flat a = snd <$> M.toDescList a

insert :: (Int, Operator Parser a) -> Table a -> Table a
insert (a,b) xs = M.insertWith (<>) a [b] xs

insert' :: [(Int, Operator Parser a)] -> Table a -> Table a
insert' xs ys = foldr insert ys xs


pInfix :: Parser Expr
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
    PE{btable, ..} <- get
    put (PE{btable = insert (f, binary t op) btable, ..})
    return (Decl $ Op op t f)

pPostfix :: Parser Expr
pPostfix = lexeme $ do
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
            exs <- S.fromList <$> pExtensions `sepBy1` symbol ","
            put PE{exts = S.union e exs, ..}
            return (Pragma $ EXT exs)
        "meta" -> do
            bar
            Meta <$> expr
        other -> do
            setOffset o
            fail ("unsupported pragma: " <> other)


curly :: Parser a -> Parser a
curly = between (symbol "{") (symbol "}")

argsTo :: Parser a -> Parser b -> Parser [b]
argsTo p a = choice
    [
        p $> []
    ,   (<>) <$> (return <$> a) <*> argsTo p a
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
    <*> ((construct <$> argsTo (symbol "->") name) >>= (\a -> a <$> expr)) -- zero or some other args and -> followed by expr

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
pLet = lexeme (Let <$> (keyword "let" *> name) <*> (((construct <$> argsTo (symbol "=") name) >>= (\a -> a <$> expr)) <|> (symbol "=" *> expr)) <*> (keyword "in" *> expr))

-- TODO: pattern matching and stuff combinators
-- "c" in name for COMBINATOR

cIfTurnedOn :: Extension -> Parser a -> Parser a -> Parser a
cIfTurnedOn ext a b = do
    es <- exts <$> get
    if ext `elem` es
        then a
        else b

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
    PE{tmodule, ..} <- get
    case tmodule of
        Nothing -> do
            keyword "module"
            mod <- Module <$> pName `sepBy1` symbol "." <?> "module name"
            put PE{tmodule = Just mod, ..}
            return (Decl mod)
        Just a -> do
            fail "module had been already declared"


pFix :: Parser Expr
pFix = Fix <$> lexeme (keyword "fix" *> expr)

fromMaybe :: (Maybe a) -> [a]
fromMaybe Nothing = []
fromMaybe (Just a) = [a]

term :: Parser Expr
term =
    choice
        [
            try (parens pOp)
        ,   parens expr
        ,   pFix
        -- ,   cIfTurnedOn PatternMatching pPLam pLam -- for example
        ,   pIf
        ,   pLam
        ,   pLet
        ,   pVar
        ,   pDataConstructor
        ,   pNum
        ]

top :: Parser Expr
top = 
    choice
        [
            try pInfixDecl
        ,   try pDataDecl
        ,   try pDecl
        ,   try pType
        ,   pModule
        ,   pImport
        ,   pInfix
        ,   pPostfix
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
expr = lexeme $ do
    optional spaces
    e <- get
    makeExprParser (top <|> try pApp <|> term) (flat $ utable e <> btable e) -- WORKS!!!!!

test :: Show a => Parser a -> Text -> IO ()
test p t = case evalState (runParserT p "<input>" t) initPE of
    Right x -> print x
    Left e -> putStrLn $ errorBundlePretty e

testIO :: IO ()
testIO = do
    line@(l:ls) <- getLine
    case l of
        '@' -> putStr "Exiting..."
        '!' -> do
            let mov = case ls of
                    "d" -> show . ddata
                    "t" -> show . dtypes
            (_, pe@PE{..}) <- exec pSource <$> (putStr "expr> " >> T.pack <$> getLine)
            putStrLn (mov pe) >> testIO
        _ -> test (fst <$> pSource) (T.pack line) >> testIO

-- Top-Level Parsers

ticks :: Parser a -> Parser a
ticks = between (symbol "`") (symbol "`")

pDecl :: Parser Expr
pDecl = Decl <$> (Const <$> (parens pOp' <|> name) <*> (((construct <$> argsTo (symbol "=") name) >>= (\a -> a <$> expr)) <|> (symbol "=" *> expr)))

pInfixDecl :: Parser Expr
pInfixDecl = Decl <$> do
    l <- name
    op <- (pOp' <|> ticks name)
    r <- name
    symbol "="
    e <- expr
    return (Const op (Lam l (Lam r e)))

pApp :: Parser Expr
pApp = lexeme $ (\a b -> foldl App a b) <$> term <*> some term <* notFollowedBy (keyword "=" <|> keyword "->"  <|> keyword "in" <|> keyword "where" <|> (pDecl $> T.empty) <|> (pType $> T.empty))

pIf :: Parser Expr
pIf = do
    keyword "if"
    e1 <- expr
    keyword "then"
    e2 <- expr
    keyword "else"
    e3 <- expr
    return (If e1 e2 e3)

pDataName :: Parser Text
pDataName = lexeme (T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar))

pDataConstructor :: Parser Expr
pDataConstructor = DataC <$> pDataName

-- | Types

pTypeVar :: Parser TypeVar
pTypeVar = TVar <$> name

pTypeConst :: Parser Type
pTypeConst = TypeConstant <$> pDataName

pForall :: Parser [TypeVar]
pForall = do
    keyword "forall"
    vars <- argsTo (symbol ".") pTypeVar
    return vars

pTypeE :: Parser Type
pTypeE = 
    choice
        [
            TypeVar <$> pTypeVar
        ,   pTypeConst
        ]

pTypeExpr :: Parser Type
pTypeExpr = do
    e <- get
    makeExprParser pTypeE (flat (typetable e)) -- WORKS!!!!!

pType :: Parser Expr
pType = lexeme $ do
    n <- (name <|> parens pOp')
    symbol "::"
    f <- optional $ pForall
    t <- pTypeExpr
    PE{dtypes, ..} <- get
    case f of
        Just fl -> do 
            put (PE{dtypes = M.singleton n (Forall fl t) <> dtypes, ..})
            return (TypeOf n (Forall fl t))
        Nothing -> do
            put (PE{dtypes = M.singleton n (Forall [] t) <> dtypes, ..})
            return (TypeOf n (Forall [] t)) -- TODO: add generalization, when no forall specified [for convenience]

-- typeExpr :: Parser Scheme

-- TODO: type application and KINDS and stuff and maybe CONSTRAINTS

-- pTypeSig :: Parser Expr -- TODO: type level operators and makeExprParser for them (maybe use state?)
-- pTypeSig = do

-- TODO: indentations (tabs and so on)

-- | TODO: Data types, but really not

pDataDecl :: Parser Expr
pDataDecl = do
    keyword "data"
    n <- pDataName
    cs' <- optional $ do
        symbol "="
        pDataName `sepBy1` symbol "|"
    let cs = case cs' of
            Nothing -> []
            Just a -> a
    let d = Data n cs
    PE{..} <- get
    let t = M.fromList (fmap (\a -> (a, (Forall [] (TypeConstant n)))) cs)
    put PE{ddata = d:ddata, dtypes = t <> dtypes, ..}
    return (Decl d)
-- demo of data types, just for defining bool, but it can be expanded thru time

-- | Testing

exec p t = runState (runParserT p "input" t) initPE

pSource :: Parser ([Expr], PE)
pSource = do
    e <- some expr
    PE{..} <- get
    return (e, PE{..})