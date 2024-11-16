import TTFPI.Basic

import Mathlib.Data.Finset.Basic

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

def fv : Typ → Finset Name
| var x => {x}
| arrow M N => M.fv ∪ N.fv
| pi x _ M => M.fv \ {x}

def subst (A : Typ) (α : Name) (B : Typ) : Typ :=
  match A with
  | var α' => if α = α' then B else A
  | arrow σ τ => arrow (σ.subst α B) (τ.subst α B)
  | pi α' k body => if α = α' ∨ α' ∈ B.fv then A else pi α' k (body.subst α B)

syntax term "[" term ":=" term ("," term)? "]" : term
macro_rules
| `($M[$x := $N]) => `(subst $M $x $N)

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

inductive Declaration where
| type (decl : Name × Typ)
| kind (decl : Name × Kind)
deriving Repr, DecidableEq

instance : Coe (Name × Typ) Declaration := ⟨.type⟩
instance : Coe (Name × Kind) Declaration := ⟨.kind⟩

abbrev Context := Finset Declaration

@[aesop safe [constructors]]
inductive Judgement : Context → Term → Typ → Prop where
| var {Γ : Context} {x : Name} {σ : Typ} :
    ↑(x, σ) ∈ Γ →
    Judgement Γ x σ
| app {Γ : Context} {M N : Term} {σ τ : Typ} :
    Judgement Γ M (σ ⇒ τ) →
    Judgement Γ N σ →
    Judgement Γ (M ∙ N) τ
| abs {Γ : Context} {x : Name} {M : Term} {σ τ : Typ} :
    Judgement (insert ↑(x, σ) Γ) M τ →
    Judgement Γ (Term.abs x σ M) (σ ⇒ τ)
-- 3.3.1: Second order abstraction rule
| tabs {Γ : Context} {α : Name} {M : Term} {A : Typ} :
    Judgement (insert ↑(α, ∗) Γ) M A →
    Judgement Γ (Λ α : ∗, M) (Π α : ∗, A)
-- 3.3.2: Second order application rule
| tapp {Γ : Context} {α : Name} {M : Term} {A B : Typ} :
    Judgement Γ M (Π α : ∗, A) →
    -- Judgement Γ B ∗ →
    Judgement Γ (M ∙ₜ B) (A[α := B])

notation Γ " ⊢ " M " : " σ => Judgement Γ M σ

def Statement (M : Term) (σ : Typ) : Prop := ∃ Γ : Context, Γ ⊢ M : σ

notation "⊢ " M " : " σ => Statement M σ

end SecondOrder
