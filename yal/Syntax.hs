{-#
    LANGUAGE
        PatternSynonyms
#-}

module Syntax where

import Data.Text (Text)
import Data.Set (Set)
import Data.Map (Map)

type Extensions = Set Extension
type Name = Text

type Program = [Declaration]

-- | General Syntax

data Literal
    = Number Int
    | Text Text
    | Character Char
    deriving (Show, Eq, Ord)

data Expr
    = Var Name
    | Constructor Name
    | App Expr Expr
    | Lam Pattern Expr -- Lam [Pattern] Expr
    | Let Name Expr Expr
    | Lit Literal
    | If Expr Expr Expr
    | Fix Expr
    | Infix Name Expr Expr
    | Postfix Name Expr
    | Case Expr [Alt]

    deriving (Show, Eq, Ord)

type Alt = (Pattern, Expr) -- Alt = ([Pattern], Expr)

data Declaration
    = Op Name I Int
    | Import [Name] [Quantifier]
    | Pragma Pragma
    | Module [Name]
    | Const Name Expr -- Const Name [Pattern] Expr
    | TypeOf Name Scheme
    | Meta Expr
    | Data Name [(Name, Scheme)] -- since we dont have args yet 
    deriving (Show, Eq, Ord)    

-- data Bool <args> = <constructor> <args> [<OR> ...]

data Quantifier
    = Hiding [Text]
    | Qualified Text
    | From Text -- PackageImports
    deriving (Show, Eq, Ord)

data Pragma
    = FFI Language Text -- represents ffi from <lang> in form of textual representation of source code, which can be parsed later
    | EXT Extensions -- extension
    | OPTS Text -- compiler options
    -- e. g.
    deriving (Show, Eq, Ord)

data Language
    = Haskell
    | CLang
    deriving (Show, Eq, Ord)

data Extension
    = LowPrecedenceOperators
    | HighPrecedenceOperators
    | AnyPrecedenceOperators
    | LinearTypes
    | DependentTypes -- one day probably
    | LazyEvaluation -- one day probably
    | PatternMatching -- pretty small amount but
    | PostfixOperators
    | PackageImports
    | ParitalLaziness
    | MultiCase
    | None
    deriving (Show, Eq, Ord)

infixr 6 $>
a $> b = b <$ a

data I = N | L | R | Post
    deriving (Show, Eq, Ord)

-- | Types
newtype TypeVar = TVar Name
    deriving (Show, Eq, Ord)
data Type =
    TypeVar TypeVar             |
    TypeConstant Name           |
    TypeArrow Type Type         |
    NoType
    deriving (Show, Eq, Ord)
data Scheme =
    Forall [TypeVar] Type
    deriving (Show, Eq, Ord)

infixr `TypeArrow`
infixr :->
pattern (:->) a b <- (a `TypeArrow` b)
    where (:->) = (TypeArrow)

-- | Errors

data Error
    = UnificationFail Type Type
    | InfiniteType TypeVar Type
    | NotInSignature TypeVar
    | UnboundVariable Name
    | ShouldHaveArgs Int Int
    | MultipleDeclaration Name
    | EndOfType
    | NoMatchingPatterns
    | NoSuchVariable Name
    | TypesMismatch Name Scheme Scheme
    | CannotCallUncallable
    | NoMainFunction
    | UnknownError
    | TODO
    deriving (Show, Eq, Ord)

-- | Values

type Env = Map Name Value

data Value
    = LamV Env Pattern Value       -- lambda
    | ConV Name [Value]    -- constructor
    | LitV Literal
    | VarV Name     -- delete it
    deriving (Show, Eq, Ord)

data Pattern
    = WildcardP
    | DataConstructorP Name [Pattern]
    | VariableP Name
    | LiteralP Literal
    -- | EmptyP
    deriving (Show, Eq, Ord)