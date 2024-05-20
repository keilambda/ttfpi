import Batteries.Data.RBMap.Basic

-- 1.3.2: The set Λ of all λ-terms
@[reducible] def Name := String

inductive Λ where
| var : Name → Λ
| app : Λ → Λ → Λ
| abs : Name → Λ → Λ
deriving Repr, BEq, Ord

namespace Λ

-- 1.3.5: Multiset of subterms
def Sub (t : Λ) : List Λ :=
  match t with
  | var _ => [t]
  | app M N => t :: (Sub M ++ Sub N)
  | abs _ M => t :: Sub M

def Subterm (L M : Λ) : Prop := L ∈ Sub M

-- instance : LawfulBEq Λ where
--   eq_of_beq beq := rfl
--   rfl := _
-- instance (L : Λ) (M : Λ) : Decidable (Subterm L M) :=
--   List.instDecidableMemListInstMembershipList L (Sub M)

-- 1.3.6
theorem Reflexivity (M : Λ) : Subterm M M := by
  sorry
  -- simp [Subterm, Sub]

theorem Transitivity (L M N : Λ) : Subterm L M ∧ Subterm M N → Subterm L N := sorry

-- 1.3.8: Proper subterm
def ProperSubterm (L M : Λ) : Prop := Subterm L M ∧ L ≠ M

-- 1.4.1: The set of free variables of a λ-term
def FreeVariables : Λ → Batteries.RBSet Λ compare
| t@(var _) => Batteries.RBSet.single t
| app M N => FreeVariables M ∪ FreeVariables N
| abs x M => FreeVariables M \ Batteries.RBSet.single (var x)

-- 1.4.3: Closed λ-term; combinator; Λ⁰
def Closed (M : Λ) : Prop := FreeVariables M = ∅

-- 1.5.1: Renaming; Mˣ ʸ; =ₐ
def rename (x y : Name) : Λ → Λ
| t@(var z) => if z == x then var y else t
| app M N => app (rename x y M) (rename x y N)
| abs z M => abs (if z == x then y else z) (if z == x then M else rename x y M)

def Renaming (M : Λ) (x y : Name) (N : Λ) : Prop := rename x y M = N

-----

def ex : Λ := abs "x" (app (var "x") (var "y"))

#eval Sub ex
-- #eval Subterm (var "x") ex
-- #eval ProperSubterm (var "x") ex
#eval FreeVariables ex
#eval FreeVariables $ app (var "x") (abs "x" (app (var "x") (var "y")))
-- #eval Closed $ abs "x" (var "x")
#eval rename "x" "a" ex |> rename "x" "b"

end Λ
