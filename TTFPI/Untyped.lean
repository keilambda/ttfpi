import TTFPI.Basic
import LeanCopilot

-- 1.3.2: The set Λ of all λ-terms
abbrev Name := String

inductive Λ where
| var : Name → Λ
| app : Λ → Λ → Λ
| abs : Name → Λ → Λ
deriving Repr, BEq, Ord

namespace Λ

-- 1.3.5: Multiset of subterms
@[simp] def Sub (t : Λ) : List Λ :=
  match t with
  | var _ => [t]
  | app M N => t :: (Sub M ++ Sub N)
  | abs _ M => t :: Sub M

@[simp] def Subterm (L M : Λ) : Prop := L ∈ Sub M

@[simp] instance : HasSubset Λ := ⟨Subterm⟩

-- 1.3.6
theorem reflexivity (M : Λ) : M ⊆ M := by
  cases M <;> simp

theorem transitivity (L M N : Λ) (hlm : L ⊆ M) (hmn : M ⊆ N) : L ⊆ N := by
  induction N with
  | var _ => simp_all
  | app M N ihlm ihln =>
    simp_all
    rename_i M'
    cases hmn with
    | inl hmn => simp_all
    | inr hmn => cases hmn <;> simp_all
  | abs x M ih =>
    simp_all
    cases hmn <;> simp_all

-- 1.3.8: Proper subterm
@[simp] def ProperSubterm (L M : Λ) : Prop := L ⊆ M ∧ L ≠ M

@[simp] instance : HasSSubset Λ := ⟨ProperSubterm⟩

-- 1.4.1: The set of free variables of a λ-term
def FV : Λ → RBSet Λ
| t@(var _) => .single t
| app M N => FV M ∪ FV N
| abs x M => FV M \ .single (var x)

-- 1.4.3: Closed λ-term; combinator; Λ⁰
def Closed (M : Λ) : Prop := FV M = ∅

-- 1.5.1: Renaming; Mˣ ʸ; =ₐ
def rename (x y : Name) : Λ → Λ
| t@(var z) => if z == x then var y else t
| app M N => app (rename x y M) (rename x y N)
| abs z M => abs (if z == x then y else z) (if z == x then M else rename x y M)

def Renaming (M : Λ) (x y : Name) (N : Λ) : Prop := rename x y M = N

-----

def ex : Λ := abs "x" (app (var "x") (var "y"))

#eval Sub ex
-- #eval (var "x") ⊆ ex
-- #eval (var "x") ⊂ ex
#eval FV ex
#eval FV $ app (var "x") (abs "x" (app (var "x") (var "y")))
-- #eval Closed $ abs "x" (var "x")
#eval rename "x" "a" ex |> rename "x" "b"

example (P Q R : Prop) : (P → Q) ∧ (Q → R) → (P → R) := by
  simp
  intros hPQ hQR hP
  apply hQR
  apply hPQ
  assumption

end Λ
