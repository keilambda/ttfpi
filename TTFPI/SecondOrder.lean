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
| arrow dom codom => s!"({dom.toString} → {codom.toString})"
| pi binder kind body => s!"(Π {binder} : {kind}. {body.toString})"

instance : ToString Typ := ⟨Typ.toString⟩

instance : Coe Name Typ := ⟨var⟩

infixr:20 " ⇒ " => arrow

syntax "Π" (term ":" term),+ "↦" term : term
macro_rules
| `(Π $binder : $kind ↦ $M) => `(pi $binder $kind $M)
| `(Π $binder : $kind, $[$binders : $kinds],* ↦ $M) => do
  let N ← `(Π $[$binders : $kinds],* ↦ M)
  `(pi $binder $kind $N)

def FTV : Typ → Finset Name
| var x => {x}
| arrow M N => M.FTV ∪ N.FTV
| pi x _ M => M.FTV \ {x}

def subst (A : Typ) (α : Name) (B : Typ) : Typ :=
  match A with
  | var α' => if α = α' then B else A
  | arrow σ τ => arrow (σ.subst α B) (τ.subst α B)
  | pi α' k body => if α = α' ∨ α' ∈ B.FTV then A else pi α' k (body.subst α B)

syntax term "[" term ":=" term ("," term)? "]" : term
macro_rules
| `($M[$x := $N]) => `(subst $M $x $N)

end Typ

-- 3.4.1: Second order pre-typed λ-terms
inductive Term where
| var (name : Name)
| app (fn : Term) (arg : Term)
| tapp (fn : Term) (arg : Typ)
| abs (param : Name) (type : Typ) (body : Term)    -- (*, *)
| tabs (binder : Name) (kind : Kind) (body : Term) -- (□, *)
deriving Repr, DecidableEq

namespace Term

protected def toString : Term → String
| var α => α
| app fn arg => s!"({fn.toString} {arg.toString})"
| tapp fn arg => s!"({fn.toString} {arg.toString})"
| abs param type body => s!"(λ{param} : {type}. {body.toString})"
| tabs binder kind body => s!"(Λ{binder} : {kind}. {body.toString})"

instance : ToString Term := ⟨Term.toString⟩

instance : Coe Name Term := ⟨var⟩

infixl:100 " ∙ " => app

infixl:100 " ∙ₜ " => tapp

syntax "Λ" (term ":" term),+ "↦" term : term
macro_rules
| `(Λ $binder : $kind ↦ $M) => `(tabs $binder $kind $M)
| `(Λ $binder : $kind, $[$binders : $kinds],* ↦ $M) => do
  let N ← `(Λ $[$binders : $kinds],* ↦ $M)
  `(tabs $binder $kind $N)

syntax "ƛ" (term ":" term),+ "↦" term : term
macro_rules
| `(ƛ $var : $type ↦ $M) => `(abs $var $type $M)
| `(ƛ $var : $type, $[$vars : $types],* ↦ $M) => do
  let N ← `(ƛ $[$vars : $types],* ↦ $M)
  `(abs $var $type $N)

end Term

-- 3.4.3: Declaration
inductive Declaration where
| type (decl : Name × Typ)
| kind (decl : Name × Kind)
deriving Repr, DecidableEq

instance : Coe (Name × Typ) Declaration := ⟨.type⟩
instance : Coe (Name × Kind) Declaration := ⟨.kind⟩

abbrev Context := Finset Declaration

/-
**Kind judgment** asserts type of the type.

NOTE:
Seems unnecessary, because every type in λ2 has a kind `∗`. I guess the author introduced it early on, so that later the
reader will need to *just* extend the definition with new rules and call it a day.
-/
@[aesop safe [constructors]]
inductive HasKind : Context → Typ → Kind → Prop where
| var {Γ : Context} {x : Name}
    ---------------
    : HasKind Γ x ∗

| arrow {Γ : Context} {σ τ : Typ} :
    HasKind Γ σ ∗
    → -----------
    HasKind Γ τ ∗
    → -----------------
    HasKind Γ (σ ⇒ τ) ∗

@[aesop safe [constructors]]
inductive HasType : Context → Term → Typ → Prop where
| var {Γ : Context} {x : Name} {σ : Typ} :
    ↑(x, σ) ∈ Γ →
    HasType Γ x σ
| app {Γ : Context} {M N : Term} {σ τ : Typ} :
    HasType Γ M (σ ⇒ τ) →
    HasType Γ N σ →
    HasType Γ (M ∙ N) τ
| abs {Γ : Context} {x : Name} {M : Term} {σ τ : Typ} :
    HasType (insert ↑(x, σ) Γ) M τ →
    HasType Γ (Term.abs x σ M) (σ ⇒ τ)
-- 3.3.1: Second order abstraction rule
| tabs {Γ : Context} {α : Name} {M : Term} {A : Typ} :
    HasType (insert ↑(α, ∗) Γ) M A →
    HasType Γ (Λ α : ∗ ↦ M) (Π α : ∗ ↦ A)
-- 3.3.2: Second order application rule
| tapp {Γ : Context} {α : Name} {M : Term} {A B : Typ} :
    HasType Γ M (Π α : ∗ ↦ A) →
    HasKind Γ B ∗ →
    HasType Γ (M ∙ₜ B) (A[α := B])

notation Γ " ⊢ " M " : " σ => HasType Γ M σ
notation Γ " ⊢ₖ " σ " : " k => HasKind Γ σ k

-- 3.4.3: Statement
def Statement (M : Term) (σ : Typ) : Prop := ∃ Γ : Context, Γ ⊢ M : σ
def KindStatement (σ : Typ) (k : Kind) : Prop := ∃ Γ : Context, Γ ⊢ₖ σ : k

notation "⊢ " M " : " σ => Statement M σ
notation "⊢ₖ " σ " : " k => KindStatement σ k

namespace Combinators

def id : Term := Λ "α" : ∗ ↦ ƛ "x" : "α" ↦ "x"
def D : Term := Λ "α" : ∗ ↦ ƛ "f" : ("α" ⇒ "α"), "x" : "α" ↦ "f" ∙ ("f" ∙ "x")
def compose : Term :=
  Λ "α" : ∗, "β" : ∗, "γ" : ∗ ↦
  ƛ "f" : ("α" ⇒ "β"), "g" : ("β" ⇒ "γ"), "x" : "α" ↦
  "g" ∙ ("f" ∙ "x")

end Combinators

end SecondOrder
