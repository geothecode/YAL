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
type Alt = ([Pattern], Maybe Expr, Expr)
type Env = Map Name Value
type Thunk = Either Expr Value -- if i add heap and gc one day

-- | General Syntax

data Literal
    = Number Integer
    | Character Char
    deriving (Show, Eq, Ord)

data Expr
    = Var Name
    | Con Name
    | App Expr Expr
    | Lam Pattern Expr -- Lam [Pattern] Expr
    -- | LamCase [Alt]
    | Let Declaration Expr
    | Lit Literal
    | If Expr Expr Expr
    | Fix Expr
    | Infix Name Expr Expr
    | Postfix Name Expr
    | Case [Expr] [Alt]
    deriving (Show, Eq, Ord)

-- | Values

data Value
    = LamV Env Pattern Expr     -- lambda
    -- | LamCaseV Env [Alt] 
    | ConV Name [Value]         -- constructor
    | LitV Literal
    -- | FAppV Name [Value]        -- variable application
    deriving (Show, Eq, Ord)

data Pattern
    = WildP
    | ConP Name [Pattern]
    | VarP Name
    | LitP Literal
    -- | EmptyP
    deriving (Show, Eq, Ord)

data Declaration
    = Op Name I Int
    | Import [Name] [Quantifier]
    | Pragma Pragma
    | Module [Name]
    | Const Name Alt -- f a | 3 > 2 = a + 4 := Const "f" [VarP "a"] (Just (3 > 2)) (Var "a" + 4)
    | TypeOf Name Scheme
    | Meta Expr
    | Data Name -- [(Name, Scheme)] -- since we dont have args yet 
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

    -- Typing
    = UnificationFail Type Type
    | InfiniteType TypeVar Type
    | NotInSignature TypeVar
    | UnboundVariable Name
    | ShouldHaveArgs Integer Integer
    | MultipleDeclaration Name
    | EndOfType
    | NoSuchVariable Name
    | TypesMismatch Name Scheme Scheme
    | TypesDontMatch

    -- Evaluation
    | CannotCallUncallable
    | NoMatchingPatterns
    | NoMainFunction
    | NotCompletePatterns
    | DifferentAmountOfArgs
    | NotInMainModule
    | Undefined

    -- File System
    | NoModule Name
    | NoPackage Name

    -- Custom
    | UnknownError
    | TODO Name
    deriving (Show, Eq, Ord)

data Command
    = ClearConsole
    | QuitSession
    | PrintEnv
    | CallCommand
    | WhichType
    deriving (Show, Eq, Ord)