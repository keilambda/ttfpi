import TTFPI.Basic

import Aesop

-- 1.3.2: The set Λ of all λ-terms
abbrev Name := String

inductive Λ where
| var : Name → Λ
| app : Λ → Λ → Λ
| abs : Name → Λ → Λ
deriving Repr, BEq, Ord, DecidableEq

namespace Λ

protected def toString : Λ → String
| var name => name
| app M N => s!"({Λ.toString M} {Λ.toString N})"
| abs x M => s!"(λ{x}. {Λ.toString M})"

instance : ToString Λ := ⟨Λ.toString⟩

def subst (t : Λ) (x : Name) (N : Λ) : Λ :=
  match t with
  | var y => if x = y then N else t
  | app L M => app (L.subst x N) (M.subst x N)
  | abs y M => if x = y then t else abs y (M.subst x N)

syntax term "[" term ":=" term "]" : term
macro_rules
| `($M[$x := $N]) => `(subst $M $x $N)

def reduceβ (t : Λ) : Λ :=
  match t with
  | app (abs x M) N => M[x := N]
  | app M N => app M.reduceβ N.reduceβ
  | abs y N => abs y N.reduceβ
  | var _ => t

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
    cases hmn
    · simp_all
    · aesop
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
def rename (t : Λ) (x y : Name) : Λ :=
  match t with
  | var x' => if x' = x then var y else t
  | app M N => app (M.rename x y) (N.rename x y)
  | abs x' M => if x' ≠ x then abs x' (M.rename x y) else t

inductive AlphaEq : Λ → Λ → Prop where
| rename {x y : Name} {M N : Λ} : (.var y) ∉ FV M → N = rename M x y → AlphaEq (abs x M) (abs y N)
| compatApp {M N : Λ} : AlphaEq M N → AlphaEq (app M L) (app N L) → AlphaEq (app L M) (app L N)
| compatAbs {z : Name} {M N : Λ} : AlphaEq (abs z M) (abs z N)
| refl (M : Λ) : AlphaEq M M
| symm {M N : Λ} : AlphaEq M N → AlphaEq N M
| trans {L M N : Λ} : AlphaEq L M → AlphaEq M N → AlphaEq L N

/- playground -/

def I : Λ := abs "x" (var "x")
def ex : Λ := abs "x" (app (var "x") (var "y"))

#eval ex.subst "y" I |> toString
#eval ex["y" := I] |> toString
#eval (app I (var "x")).reduceβ |> toString

#eval Sub ex |> toString
-- #eval (var "x") ⊆ ex
-- #eval (var "x") ⊂ ex
#eval FV ex
-- #eval (var "y") ∈ (FV ex)
#eval FV $ app (var "x") (abs "x" (app (var "x") (var "y")))
-- #eval Closed $ abs "x" (var "x")
#eval ex.rename "x" "a" |>.rename "x" "b" |> toString

def M := (Λ.app (.abs "x" (.var "y")) (.var "z"))

#eval M.toString

#eval Λ.subst M "x" (.var "y") |> toString
#eval Λ.subst M "z" (.var "y") |> toString
#eval Λ.reduceβ M

/- playground -/

end Λ
