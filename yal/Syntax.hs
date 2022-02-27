{-#
    LANGUAGE
        PatternSynonyms
#-}

module Syntax where

import Data.Text (Text)
import Data.Set (Set)

type Extensions = Set Extension
type Name = Text

-- | General Syntax

data Literal
    = Number Int
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
    | TypeOf Name Scheme
    | Decl Declaration
    | Meta Expr
    deriving (Show, Eq, Ord)

data Declaration
    = Op Name I Int
    | Warning Name
    | Import [Name] [Quantifier]
    | Module [Name]
    | Const Name Expr
    | Data Name [Name] -- since we dont have args yet 
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

data TypeCheckerError
    = UnificationFail Type Type
    | InfiniteType TypeVar Type
    | NotInSignature TypeVar
    | UnboundVariable Name
    deriving (Show, Eq, Ord)
