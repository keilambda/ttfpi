import TTFPI.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Order.Heyting.Basic

/-
# Simply Typed λ-calculus: λ→
-/

-- 2.2.1: The set Typ of all simple types
inductive Typ where
| var (α : Name)
| arrow (σ : Typ) (τ : Typ)
deriving Repr, DecidableEq

namespace Typ

protected def toString : Typ → String
| var α => α
| arrow σ τ => "(" ++ σ.toString ++ " → " ++ τ.toString ++ ")"

instance : ToString Typ := ⟨Typ.toString⟩

instance : Coe Name Typ := ⟨var⟩

infixr:20 " ⇒ " => arrow

end Typ

-- 2.4.1: Pre-typed λ-terms
inductive Term where
| var (name : Name)
| app (fn : Term) (arg : Term)
| abs (param : Name) (type : Typ) (body : Term)
deriving Repr

namespace Term

protected def toString : Term → String
| var name => name
| app M N => s!"({M.toString} {N.toString})"
| abs x σ M => s!"(λ{x} : {σ}. {M.toString})"

instance : ToString Term := ⟨Term.toString⟩

instance : Coe Name Term := ⟨var⟩

infixl:100 " ∙ " => app

def FV : Term → Finset Name
| var x => {x}
| app M N => FV M ∪ FV N
| abs x _ M => FV M \ {x}

end Term

-- 2.4.2: Statement, declaration, context, judgement
abbrev Declaration := Name × Typ
abbrev Context := Finset Declaration

-- 2.4.5: Derivation rules for λ→
@[aesop safe [constructors]]
inductive Judgement : Context → Term → Typ → Prop where
| var (Γ : Context) (x : Name) (σ : Typ) :
    (x, σ) ∈ Γ →
    Judgement Γ x σ
| app (Γ : Context) (M N : Term) (σ τ : Typ) :
    Judgement Γ M (σ ⇒ τ) →
    Judgement Γ N σ →
    Judgement Γ (M ∙ N) τ
| abs (Γ : Context) (x : Name) (M : Term) (σ τ : Typ) :
    Judgement (insert (x, σ) Γ) M τ →
    Judgement Γ (Term.abs x σ M) (σ ⇒ τ)

notation Γ " ⊢ " M " : " σ => Judgement Γ M σ

def Statement (M : Term) (σ : Typ) : Prop := ∃ Γ : Context, Γ ⊢ M : σ

notation "⊢ " M " : " σ => Statement M σ

-- 2.2.7: Typeable term
def Typeable (M : Term) : Prop := ∃ σ : Typ, ⊢ M : σ

-- 2.4.10: Legal λ→-terms
def Legal (M : Term) : Prop := ∃ Γ ρ, Γ ⊢ M : ρ

-- 2.10.1: Domain, dom, subcontext, ⊆, permutation, projection
def dom (Γ : Context) : Finset Name := Γ.image Prod.fst
def Subcontext (Γ Δ : Context) : Prop := Δ ⊆ Γ
def Permutation (Γ Δ : Context) : Prop := dom Δ = dom Γ
def projection (Γ : Context) (Φ : Finset Name) : Context := Γ.filter (·.1 ∈ dom Γ ∩ Φ)

infix:60 " ↾ " => projection

-- 2.10.3: Free Variables Lemma
theorem dom_insert_eq_insert_dom {Γ : Context} {x : Name} {σ : Typ} : dom (insert (x, σ) Γ) = insert x (dom Γ) := by
  simp [dom]

theorem Finset.diff_subset_iff {α : Type*} [DecidableEq α] {s t u : Finset α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  show s \ t ≤ u ↔ s ≤ t ∪ u from sdiff_le_iff

theorem context_free_variables {Γ : Context} {L : Term} {σ : Typ} (J : Γ ⊢ L : σ) : L.FV ⊆ dom Γ := by
  induction J with
  | var Δ x α h =>
    simp [Term.FV, dom]
    exact ⟨α, h⟩
  | app Δ M N α β jM jN ihM ihN =>
    simp [Term.FV]
    apply Finset.union_subset
    · exact ihM
    · exact ihN
  | abs Δ x M α β Δ' ihM =>
    simp [Term.FV]
    simp [dom_insert_eq_insert_dom] at ihM
    exact Finset.diff_subset_iff.mpr ihM
