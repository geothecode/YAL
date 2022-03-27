module Debug where

import Syntax

ch a = Lit $ Character a
nm a = Lit $ Number a
nmp a = LitP $ Number a
tx a = foldr App (Con "TextNil") (App (Con "TextCons") <$> ch <$> a)

vr a = Var a
vrp a = VarP a
cn a = Con a
cnp a = ConP a
i op e1 e2 = Infix op e1 e2

tv a = TypeVar (TVar a)
tc a = TypeConstant a
