import Mathlib.Data.Finset.Basic

/-
# Simply Typed λ-calculus: λ→
-/

abbrev Name := String

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

infix:25 " ⇒ " => arrow

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

end Term

-- 2.4.2: Statement, declaration, context, judgement
abbrev Declaration := Name × Typ
abbrev Context := Finset Declaration

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

notation Γ " ⊢ " M " ∶ " σ => Judgement Γ M σ

def Statement (M : Term) (σ : Typ) : Prop := ∃ Γ : Context, Γ ⊢ M ∶ σ

infix:20 " ∶ " => Statement
