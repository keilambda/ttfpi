import TTFPI.Basic

namespace SecondOrder

inductive Kind where
| star
deriving Repr, DecidableEq

notation " ∗ " => Kind.star

instance : ToString Kind := ⟨fun k => match k with | .star => "∗"⟩

inductive Typ where
| var (name : Name)
| arrow (dom : Typ) (codom : Typ)
| pi (binder : Name) (kind : Kind) (body : Typ)
deriving Repr, DecidableEq

namespace Typ

protected def toString : Typ → String
| var α => α
| arrow dom codom => s!"{dom.toString} → {codom.toString}"
| pi binder kind body => s!"Π {binder} : {kind}. {body.toString}"

instance : ToString Typ := ⟨Typ.toString⟩

instance : Coe Name Typ := ⟨var⟩

infixr:20 " ⇒ " => arrow

notation "Π" binder ":" kind "," body => pi binder kind body

end Typ

-- 3.4.1: Second order pre-typed λ-terms
inductive Term where
| var (name : Name)
| app (fn : Term) (arg : Term)
| tapp (fn : Term) (arg : Typ)
| abs (param : Name) (type : Typ) (body : Term)
| tabs (binder : Name) (kind : Kind) (body : Term)
deriving Repr, DecidableEq

namespace Term

protected def toString : Term → String
| var α => α
| app fn arg => s!"({fn.toString} {arg.toString})"
| tapp fn arg => s!"({fn.toString} [{arg.toString}])"
| abs param type body => s!"(λ{param} : {type}. {body.toString})"
| tabs binder kind body => s!"(Λ{binder} : {kind}. {body.toString})"

instance : ToString Term := ⟨Term.toString⟩

instance : Coe Name Term := ⟨var⟩

infixl:100 " ∙ " => app

infixl:100 " ∙ₜ " => tapp

notation "Λ" binder ":" kind "," body => tabs binder kind body

end Term
end SecondOrder
