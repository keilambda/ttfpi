import TTFPI.Basic

namespace SecondOrder

inductive Kind where
| star
deriving Repr, DecidableEq

notation " ∗ " => Kind.star

inductive Typ where
| var (name : Name)
| arrow (dom : Typ) (codom : Typ)
| pi (param : Name) (kind : Kind) (body : Typ)
deriving Repr, DecidableEq

-- 3.4.1: Second order pre-typed λ-terms
inductive Term where
| var (name : Name)
| app (fn : Term) (arg : Term)
| tapp (fn : Term) (arg : Typ)
| abs (param : Name) (type : Typ) (body : Term)
| tabs (param : Name) (kind : Kind) (body : Term)
deriving Repr, DecidableEq

end SecondOrder
