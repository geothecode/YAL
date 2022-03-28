module Pretty where

import Syntax

import Prelude hiding ((<>))
import Text.PrettyPrint
import Data.Text (Text)
import qualified Data.Text as T

-- | Utilities

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

ticksIf :: Bool -> Doc -> Doc
ticksIf True a = "\"" <> a <> "\""
ticksIf False a = a 

flat :: Pretty a => Int -> [a] -> Doc
flat _ [] = mempty
flat n (x:xs) = pretty n x <+> flat n xs

sepBy :: Pretty a => Int -> String -> [a] -> Doc
sepBy _ _ [] = mempty
sepBy n _ [x] = pretty n x
sepBy n del (x:xs) = pretty n x <> text del <+> sepBy n del xs

showError :: Int -> Error -> Doc
showError n e = text "error:" <+> "\n\t" <+> case e of
    UnificationFail l r -> text "unification fail:" <+> "\n\t" <+> parens (pretty n l) <+> "\n\t" <+> parens (pretty n r)
    InfiniteType tv t -> text "cannot construct infinite type:\n\t" <+> parens (pretty n tv) <+> parens (pretty n t)
    NotInSignature tv -> text "not in signature:" <+> pretty n tv
    UnboundVariable t -> text "unbound variable:" <+> text (T.unpack t)
    ShouldHaveArgs a b -> text "should have" <+> integer a <+> "arguments, but has" <+> integer b
    -- MultipleDeclaration n -> text "multiple declaration: " <+> text (T.unpack n)
    NoSuchVariable n -> text "there is no variable: " <+> text (T.unpack n)
    Mismatch name l r -> text "types mismatch in" <+> text (T.unpack name) <+> "declaration:\n\t" <+> pretty n l <+> "\n\t" <+> pretty n r
    MoreGeneral name l r -> text "next declaration of" <+> text (T.unpack name) <+> "is more general in:\n\t" <+> pretty n l <+> "\n\t" <+> pretty n r
    -- TypesDontMatch -> text "types do not match"

    CannotCallUncallable -> text "cannot call uncallable"
    NoMatchingPatterns -> text "non-exhaustive patterns"
    NoMainFunction -> text "no main function"
    DifferentAmountOfArgs -> "different amount of arguments"
    NotInMainModule -> "not in main module => cannot have main function"
    Undefined -> "undefined"

    NoModule name -> text "there is no module with name:" <+> text (T.unpack name)
    NoPackage name -> text "there is no package with name:" <+> text (T.unpack name)

    UnknownError -> text "unknown error yet :)"
    TODO msg -> text "TODO:" <+> text (T.unpack msg)

-- | Main
class Pretty a where
    pretty :: Int -> a -> Doc

instance Pretty Expr where
    pretty n (Var name) = text (T.unpack name)
    pretty n (Con name) = text (T.unpack name)
    pretty n (App l r)  = parensIf (n > 0) (pretty (n+1) l <+> pretty (n+1) r)
    pretty n (Lit lit)  = pretty n lit
    pretty n (Lam pat exp) = parensIf (n>0) ("\\" <> pretty n pat <+> "->" <+> pretty n exp)
    pretty n (Infix op l r) = parensIf (n>0) (pretty (n+1) l <+> text (T.unpack op) <+> pretty (n+1) r)
    pretty n (If c l r) = parensIf (n>0) ("if" <+> pretty n c <+> "\n\tthen" <+> pretty n l <+> "\n\telse" <+> pretty n r)
    pretty n (Postfix op e) = parens (pretty n e <> text (T.unpack op))
    pretty n (Let (Const name (pat, Nothing, expr)) exp) = "let" <+> text (T.unpack name) <+> flat n pat <+> "=" <+> pretty n expr <+> "in" <+> pretty n exp
    pretty n (Let (Const name (pat, Just cond, expr)) exp) = "let" <+> text (T.unpack name) <+> flat n pat <+> "|" <+> pretty n cond <+> "=" <+> pretty n expr <+> "in" <+> pretty n exp
    pretty n (Case exps alts) = parensIf (n>0) ("case" <+> sepBy n "," exps <+> "of" <+> "\n\t" <+> sepBy (n + 1) "\n\t" alts)

instance Pretty Alt where
    pretty n (pats, Nothing, exp) = sepBy n "," pats <+> "->" <+> pretty n exp
    pretty n (pats, Just cond, exp) = sepBy n "," pats <+> "|" <+> pretty n cond <+> "->" <+> pretty n exp

instance Pretty Pattern where
    pretty n WildP = text "_"
    pretty n (ConP name pats) = parensIf (n>0) (text (T.unpack name) <+> flat n pats)
    pretty n (VarP name) = text (T.unpack name)
    pretty n (LitP lit) = pretty n lit

instance Pretty Value where
    pretty n (ConV "TextNil" []) = mempty
    -- pretty _ (ConV "TextCons" [LitV (Character ch), text]) = let n = 1 in ticksIf (n>0) (char ch <> (pretty (n-1) text))
    pretty n (ConV "TextCons" [LitV (Character ch), text]) = char ch <> (pretty (n-1) text)
    pretty n (ConV name vals) = parensIf (n>0) (text (T.unpack name) <+> flat n vals)
    pretty n (LitV a) = pretty n a
    pretty n (LamV _ pat exp) = parensIf (n > 0) ("\\" <> pretty n pat <+> "->" <+> pretty n exp)

instance Pretty Literal where
    pretty _ (Number a) = integer a
    pretty _ (Character a) = "'" <> char a <> "'"

instance Pretty TypeVar where
    pretty _ (TVar name) = text (T.unpack name)

instance Pretty Type where
    pretty n (TypeVar a) = pretty n a
    pretty n (TypeConstant a) = text (T.unpack a)
    pretty n (TypeArrow l r) = parensIf (n>0) (pretty (n+1) l <+> "->" <+> pretty n r)
    pretty _ NoType = mempty

instance Pretty Scheme where
    pretty n (Forall [] t) = pretty n t
    pretty n (Forall fs t) = "forall" <+> flat n fs <> "." <+> pretty n t

instance Pretty Declaration where
    pretty n (TypeOf name sch) = text (T.unpack name) <+> "::" <+> pretty n sch
    pretty n (Const name (pats, Nothing, exp)) = text (T.unpack name) <+> flat n pats <+> "=" <+> pretty n exp
    pretty n (Const name (pats, Just cond, exp)) = text (T.unpack name) <+> flat n pats <+> "|" <+> pretty n cond <+> "=" <+> pretty n exp
    pretty _ _ = mempty

instance Pretty Extension where
    pretty _ _ = mempty

instance Pretty Error where
    pretty n error = showError n error

instance (Pretty a, Pretty b) => Pretty (Either a b) where
    pretty n (Left a) = pretty n a
    pretty n (Right a) = pretty n a

runPretty :: Pretty a => a -> String
runPretty = render . pretty 0