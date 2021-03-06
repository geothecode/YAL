{-#
    LANGUAGE
        OverloadedStrings,
        PatternSynonyms
#-}
module Parsing where

import Data.Text (Text)
import Data.Char (isUpper)
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
-- import Control.Monad.Trans.RWS

import Syntax
import Typing
import Pretty (runPretty)

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
    ,   declpat     :: Map Name [Expr]
    ,   sigs        :: TE
    ,   datainfo    :: Map Name (Int, Scheme)
    }

turnOn :: Extension -> Parser ()
turnOn e = do
    pe <- get
    put (pe {exts = S.insert e (exts pe)})

turnOff :: Extension -> Parser ()
turnOff e = do
    pe <- get
    put (pe {exts = S.delete e (exts pe)})

-- type Parser = ParsecT Void Text (StateT PE IO)
type Parser = ParsecT Void Text (State PE )


symbol :: Text -> Parser Text
symbol = Lexer.symbol sc

keyword :: Text -> Parser Text
keyword a = lexeme' (string a <* notFollowedBy alphaNumChar)

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
    ,   "->"
    ,   "="
    ,   "::"
    ,   "infixl"
    ,   "infixr"
    ,   "infix"
    ,   "postfix"
    ,   "case"
    ,   "of"
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

pNum :: Parser Literal
pNum = Number <$> (parens p' <|> p)
    where
        p = Lexer.decimal
        p' = negate <$> (char '-' *> Lexer.decimal)
            


parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")


-- higher = bigger precedence
initPE :: PE
initPE = PE
    {
        btable      = insert (7, InfixL (try (ticks (name <|> try (parens name) <|> parens pOp') >>= (\a -> return (Infix a))))) M.empty
    ,   utable      = mempty {- insert (9, unary' "@") $ -}
    ,   typetable   = insert (-1, InfixR (TypeArrow <$ symbol "->")) M.empty
    ,   exts        = mempty
    ,   rec         = False
    ,   lastoffset  = 0
    ,   tmodule     = Nothing
    ,   warnings    = mempty
    ,   dtypes      = mempty 
    ,   ddata       = mempty
    ,   declpat     = mempty
    ,   sigs        = mempty
    ,   datainfo    = mempty
    }
{- @ is used to reference to this particular type-variable -}

-- Maybe we should return (Var a) for unification purposes ? ISSUE:
binary :: I -> Text -> Operator Parser Expr
binary N a = InfixN (Infix a <$ symbol a <* notFollowedBy (symbol a))
binary L a = InfixL (Infix a <$ symbol a <* notFollowedBy (symbol a))
binary R a = InfixR (Infix a <$ symbol a <* notFollowedBy (symbol a))

unary :: Text -> Operator Parser Expr
unary a = Control.Monad.Combinators.Expr.Postfix (Syntax.Postfix a <$ symbol a)

flat :: Table a -> [[Operator Parser a]]
flat a = snd <$> M.toDescList a

insert :: (Int, Operator Parser a) -> Table a -> Table a
insert (a,b) xs = M.insertWith (<>) a [b] xs

insert' :: [(Int, Operator Parser a)] -> Table a -> Table a
insert' xs ys = foldr insert ys xs


pInfix :: Parser Declaration
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
        pe <- get -- setting last error offset
        put (pe {lastoffset = o})
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
    pe <- get
    put (pe {btable = insert (f, binary t op) (btable pe)})
    return (Op op t f)

pPostfix :: Parser Declaration
pPostfix = lexeme $ do
    t <- keyword "postfix" $> Post
    f <- return 9 -- mostly TODO:
    Var op <- pOp
    pe <- get
    put (pe {utable = insert (f, unary op) (utable pe)})
    return (Op op t f)



bar :: Parser Char
bar = lexeme $ char '|' 

matchlang :: String -> Language
matchlang "haskell" = Haskell
matchlang "c" = CLang

pPragma :: Parser Declaration
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
            pe <- get
            exs <- S.fromList <$> pExtensions `sepBy1` symbol ","
            put (pe {exts = S.union (exts pe) exs})
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

construct :: [Pattern] -> Expr -> Expr
-- construct [] e = Lam EmptyP e
construct xs e = foldr Lam e xs

pOp :: Parser Expr
pOp = Var <$> (T.pack <$> lexeme (some (oneOf ("+-$%&^*/?.,~@<>|#=:" :: String))))

pOp' :: Parser Text
pOp' = (T.pack <$> lexeme (some (oneOf ("+-$%&^*/?.,~@<>|#=:" :: String))))

pLam :: Parser Pattern -> Parser Expr
pLam pArgs = Lam <$> 
        ((keyword "lam" <|> symbol "\\") *> pArgs) -- lam x OR \x
    <*> ((construct <$> argsTo (symbol "->") pArgs) >>= (\a -> a <$> expr)) -- zero or some other args and -> followed by expr

pLamName :: Parser Pattern
pLamName = do
    o <- getOffset
    n <- optional (VarP <$> (name <|> parens name))
    case n of
        Just p -> return p
        Nothing -> do
            setOffset o
            fail "perhaps you meant to use <patterns> instead?"


pExtensions :: Parser Extension
pExtensions = choice
    [
        symbol "patterns" $> PatternMatching
    ,   symbol "lowops" $> LowPrecedenceOperators
    ,   symbol "highops" $> HighPrecedenceOperators
    ,   symbol "postfix" $> PostfixOperators
    ,   symbol "packageimports" $> PackageImports
    ,   symbol "multicase" $> MultiCase
    ,   do
            o <- getOffset
            n <- some letterChar
            setOffset o
            fail ("no such an extension: " <> n)
    ]   <?> "extension"

pLet :: Parser Expr
pLet = lexeme $ do
    keyword "let"
    d <- decl -- todo to some decl
    keyword "in"
    e <- expr
    return (Let d e) -- TODO


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

pImport :: Parser Declaration
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
    return (Import n $ concat $ map fromMaybe [qual, fr, hid])
    -- TODO:

pModule :: Parser Declaration
pModule = do
    pe <- get
    case tmodule pe of
        Nothing -> do
            keyword "module"
            mod <- Module <$> pName `sepBy1` symbol "." <?> "module name"
            put (pe {tmodule = Just mod})
            return mod
        Just a -> do
            fail "module had been already declared"


pFix :: Parser Expr
pFix = Fix <$> lexeme (keyword "fix" *> expr)

fromMaybe :: (Maybe a) -> [a]
fromMaybe Nothing = []
fromMaybe (Just a) = [a]


-- testIO :: IO ()
-- testIO = do
--     line@(l:ls) <- getLine
--     case l of
--         '@' -> putStr "Exiting..."
--         '!' -> do
--             let mov = case ls of
--                     "d" -> show . ddata
--                     "t" -> show . dtypes
--             (_, pe) <- exec pSource <$> (putStr "expr> " >> T.pack <$> getLine)
--             putStrLn (mov pe) >> testIO
--         _ -> test (fst <$> pSource') (T.pack line) >> testIO

-- Top-Level Parsers

ticks :: Parser a -> Parser a
ticks = between (symbol "`") (symbol "`")

-- pConstP :: Parser Declaration
-- pConstP = do
--     n <- (parens pOp' <|> name)
--     o <- getOffset
--     (e, p) <- do
--         pat <- argsTo (symbol "=") pPattern
--         exp <- expr
--         return ((construct pat $ exp), pat)
--     pe <- get
--     put (pe {declpat = M.insertWith (<>) n (return e) (declpat pe)})
--     return (Const n e)

-- pConst :: Parser Declaration
-- pConst = do
--     n <- (parens pOp' <|> name)
--     o <- getOffset
--     (e, p) <- do
--         pat <- argsTo (symbol "=") pLamName
--         exp <- expr
--         return ((construct pat $ exp), pat)
--     pe <- get
--     put (pe {declpat = M.insertWith (<>) n (return e) (declpat pe)})
--     return (Const n e)

pConst :: Parser Pattern -> Parser Declaration
pConst pArgs = do
    n <- (parens pOp' <|> name)
    pat <- pArgs `sepBy` spaces
    cond <- optional (symbol "|" *> expr)
    symbol "="
    exp <- expr
    return (Const n (pat, cond, exp))

pPattern :: Parser Pattern
pPattern = lexeme $ choice
    [
            pDataSolo
        ,   pDataPattern
        ,   pTextPattern
        ,   keyword "_" $> WildP
        ,   VarP <$> (name <|> parens name)
        ,   LitP <$> pLit'
    ]

pTextPattern :: Parser Pattern
pTextPattern = do
    e <- pText
    return (exprToPattern e)

exprToPattern :: Expr -> Pattern
exprToPattern (Var n) = VarP n
exprToPattern (Con n) = ConP n mempty
exprToPattern (Lit n) = LitP n
exprToPattern (App l@(App{}) r) = case exprToPattern l of
    ConP n a -> ConP n (a <> return (exprToPattern r))
exprToPattern (App l@(Con n) r) = ConP n (return (exprToPattern r))

pDataSolo :: Parser Pattern
pDataSolo = do
    name <- pDataName
    return (ConP name mempty)

pDataPattern :: Parser Pattern
pDataPattern = parens (do
    name <- pDataName
    args <- pPattern `sepBy` spaces
    return (ConP name args))

pInfixDecl :: Parser Declaration
pInfixDecl = do
    l <- pPattern
    op <- (pOp' <|> ticks name)
    if op == "|"
        then empty
        else do
            r <- pPattern
            symbol "="
            e <- expr
            return (Const op ([l, r], Nothing, e))

pApp :: Parser Expr
pApp = lexeme $
        (\a b -> foldl App a b)
    <$> term
    <*> some term
    <* notFollowedBy 
           ( try (choice (keyword <$> kwrds))
        <|> (pConst pLamName $> T.empty) 
        <|> (pType $> T.empty))

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
pDataConstructor = Con <$> pDataName

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

addSig :: Name -> Scheme -> TE -> TE
addSig n sc te = te {infered = M.singleton n sc <> (infered te)}

pType :: Parser Declaration
pType = lexeme $ do
    n <- (name <|> parens pOp')
    symbol "::"
    f <- optional $ pForall
    t <- pTypeExpr
    pe <- get
    case f of
        Just fl -> do 
            put (pe {sigs = addSig n (Forall fl t) (sigs pe)})
            return (TypeOf n (Forall fl t))
        Nothing -> do
            put (pe {sigs = addSig n (Forall [] t) (sigs pe)})
            return (TypeOf n (Forall [] t)) -- TODO: add generalization, when no forall specified [for convenience]

-- typeExpr :: Parser Scheme

-- TODO: type application and KINDS and stuff and maybe CONSTRAINTS

-- pTypeSig :: Parser Expr -- TODO: type level operators and makeExprParser for them (maybe use state?)
-- pTypeSig = do

-- TODO: indentations (tabs and so on)

-- | TODO: Data types, but really not

pDataArg :: Parser Type
pDataArg = (p2 <|> p1)
    where
        p1 = do
            v'@(n:ns) <- T.unpack <$> pName
            let v = T.pack v'
            if isUpper n
                then return (TypeConstant v)
                else return (TypeVar (TVar v))
        p2 = do
            t <- parens (pTypeExpr)
            return t

pDataNode :: Name -> Parser (Name, (Int, Scheme))
pDataNode base = do
    n <- pDataName
    args <- optional $ pDataArg `sepBy` sc
    case args of
        Nothing -> do
            let sc = Forall [] (TypeConstant base)
            modify (\g -> g {sigs = addSig n sc (sigs g)})
            return (n, (0, sc))
        Just a -> do
            let sc = Forall [] (foldr (:->) (TypeConstant base) a)
            modify (\g -> g {sigs = addSig n sc (sigs g)})
            return (n, (length a, sc))

-- TODO: pattern matching
pDataDecl :: Parser Declaration 
pDataDecl = do
    keyword "data"
    n <- pDataName
    cs' <- optional $ do
        symbol "="
        try (pDataNode n `sepBy1` symbol "|")
    let cs = case cs' of
            Nothing -> []
            Just a -> a
    let d = Data n
    let t = M.fromList cs
    -- modify (\pe -> pe {ddata = d:(ddata pe), dtypes = t <> dtypes pe})
    modify (\pe -> pe {datainfo = t <> (datainfo pe)})
    return d

-- | Case

-- pCaseItem :: Parser Alt
-- pCaseItem = Lexer.lexeme sc $ do
--     pat <- pPattern -- `sepBy1` symbol ","
--     symbol "->"
--     exp <- expr
--     return (pat, exp)


-- pCase :: Parser Expr
-- pCase = do
--     keyword "case"
--     e <- expr
--     keyword "of"
--     alts <- Lexer.indentBlock spaces (return (Lexer.IndentMany (Just (mkPos 5)) (return) pCaseItem))
--     return (Case e alts)

-- pCase :: Parser Expr
-- pCase = 
-- pCase :: Parser Expr
-- pCase = (try p' <|> Lexer.indentBlock spaces p)
--     where
--         p = do
--             keyword "case"
--             e <- expr
--             keyword "of"
--             return (Lexer.IndentSome Nothing (return . (\a -> App (LamCase a) e)) pCaseItem)
--         p' = do
--             keyword "case"
--             e <- expr
--             keyword "of"
--             (\a -> App a e) <$> (LamCase <$> curly (pCaseItem `sepBy` (symbol ";")))

-- pLamCase :: Parser Expr
-- pLamCase = undefined

pCaseItem :: Parser Alt
pCaseItem = Lexer.lexeme sc $ do
    pat <- pPattern `sepBy` symbol ","
    cond <- optional (symbol "|" *> expr)
    symbol "->"
    exp <- expr
    return (pat, cond, exp)

pCase :: Parser Expr
pCase = (try p' <|> Lexer.indentBlock spaces p)
    where
        p = do
            keyword "case"
            e <- expr `sepBy` symbol ","
            keyword "of"
            return (Lexer.IndentSome Nothing (return . (Case e)) pCaseItem)
        p' = do
            keyword "case"
            e <- expr `sepBy` symbol ","
            keyword "of"
            Case e <$> curly (pCaseItem `sepEndBy` (symbol ";"))

-- | Indentation-based parsing

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

lexeme' :: Parser a -> Parser a
lexeme' = Lexer.lexeme sc

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaces

sc :: Parser ()
sc = Lexer.space 
        hspace1
        pLineComment
        pBlockComment

indented :: Parser a -> Parser [a]
indented p = Lexer.lineFold spaces $ \s ->
    let ps = p `sepBy1` try s
    in ps <* spaces

-- | Summary

term :: Parser Expr
term =
    choice
        [
            -- dbg "parens op" $ 
            try (parens pOp)
        ,   
            -- dbg "parens exp" $ 
            parens expr
        ,   
            -- dbg "lit" $
            pLit
        ,   
            -- dbg "text" $ 
            try pText
        ,   
            -- dbg "case" $ 
            pCase
        ,   
            -- dbg "fix" $ 
            pFix
        ,   
            -- dbg "if" $ 
            pIf
        ,   
            -- dbg "lam" $
            cIfTurnedOn PatternMatching (pLam pPattern) (pLam pLamName)
        ,   
            -- dbg "let" $
            pLet
        ,   
            -- dbg "datacon" $
            pDataConstructor
        ,   
            -- dbg "var" $
            pVar
        ]

decl :: Parser Declaration
decl = lexeme $ do
    d <- choice
        [
            try pInfixDecl
        ,   try pDataDecl
        ,   cIfTurnedOn PatternMatching (try (pConst pPattern)) (try (pConst pLamName))
        ,   try pType
        ,   pModule
        ,   pImport
        ,   pInfix
        ,   pPostfix
        ,   cIfTurnedOn PostfixOperators pPostfix empty
        ,   pPragma
        ]
    s <- gets sigs
    case customRunTyper (typerStepD d) s of
        Left err -> fail (runPretty err)
        Right (_, te, _) -> do
            modify (\g -> g {sigs = te <> (sigs g)})
            return d

pLit' :: Parser Literal
pLit' = choice
    [
        pNum
    ,   pChar
    ]

characters :: [Char]
characters = ['a'..'z'] <> ['A'..'Z'] <> ['0'..'9'] <> "!@#$%^&*()_-+=[]{}~`|/?.,<>:;' "

escapedchars :: [Char]
escapedchars = "\'\"\n\r\a"

pChar' :: Parser Char
pChar' = oneOf characters

pChar :: Parser Literal
pChar = Character <$> lexeme (between (char '\'') (char '\'') (oneOf characters))

pLit :: Parser Expr
pLit = 
    -- Lam EmptyP <$> 
    Lit <$> lexeme pLit'

pText :: Parser Expr
pText = do
    tx <- lexeme (between "\"" "\"" (many pChar'))
    return (foldr (\a e -> App (App (Con "TextCons") (Lit (Character a))) e) (Con "TextNil") tx)

expr :: Parser Expr
expr = lexeme $ do
    e <- get
    (makeExprParser (try pApp <|> term) (flat $ utable e <> btable e))

-- | Final

test :: Show a => Parser a -> Text -> IO ()
test p t = case evalState (runParserT p "<input>" t) initPE of
    Right x -> print x
    Left e -> putStrLn $ errorBundlePretty e

-- testEnv :: Text -> IO ()
-- testEnv t = case runState (runParserT pSource "<input>" t) initPE of
--     (Right x, pe) -> do
--         print x
--         putStrLn "\nenvironment:"
--         print (declpat pe)
--     (Left e, _) -> putStrLn $ errorBundlePretty e


-- exec' p t pe = runState (runParserT p "input" t) pe

-- pSource' :: Parser ([Declaration], PE)
-- pSource' = do
--     e <- some (decl <* optional (symbol ";" <* spaces) <* optional spaces)
--     pe <- get
--     return (e, pe)

adjustPE :: PE -> PE -> PE
adjustPE pe1 pe2 = pe2 
    {
        btable = M.unionWith (<>) (btable pe1) (btable pe2)
    ,   utable = M.unionWith (<>) (utable pe1) (utable pe2)
    ,   typetable = M.unionWith (<>) (typetable pe1) (typetable pe2)
    ,   dtypes = (dtypes pe1) <> (dtypes pe2)
    ,   sigs = (sigs pe1) <> (sigs pe2)
    ,   datainfo = (datainfo pe1) <> (datainfo pe2)
    }

instance Semigroup PE where
    (<>) = adjustPE

instance Monoid PE where
    mempty = initPE

