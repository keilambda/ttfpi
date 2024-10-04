import TTFPI.Basic

import Aesop
import Mathlib.Order.Defs
import Mathlib.Order.RelClasses

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

instance : Coe Name Λ := ⟨Λ.var⟩

syntax "lam" term,+ "↦" term : term
macro_rules
| `(lam $x ↦ $M) => `(Λ.abs $x $M)
| `(lam $x, $xs:term,* ↦ $M) => do
  let N ← `(lam $xs,* ↦ $M)
  `(Λ.abs $x $N)

infixl:100 " :$ " => Λ.app

-- 1.3.5: Multiset of subterms
@[simp] def Sub (t : Λ) : List Λ :=
  match t with
  | var _ => [t]
  | app M N => t :: (Sub M ++ Sub N)
  | abs _ M => t :: Sub M

@[simp] def Subterm (L M : Λ) : Prop := L ∈ Sub M

@[simp] instance : HasSubset Λ := ⟨Subterm⟩

-- 1.3.6
@[simp] instance instIsReflInSub : IsRefl Λ (· ∈ Sub ·) where
  refl M := by
    induction M with
    | var _ => rw [Sub, List.mem_singleton]
    | app P Q => rw [Sub]; exact List.mem_cons_self ..
    | abs _ Q => rw [Sub]; exact List.mem_cons_self ..

@[simp] instance instIsReflSubterm : IsRefl Λ Subterm where
  refl M := by induction M <;> (rw [Subterm]; exact instIsReflInSub.refl ..)

@[simp] instance instIsReflSubset : IsRefl Λ Subset where
  refl M := by induction M <;> (rw [Subset, instHasSubset]; exact IsRefl.refl ..)

@[simp] instance : IsTrans Λ Subset where
  trans L M N hlm hmn := by induction N <;> aesop

instance : LawfulBEq Λ where
  eq_of_beq := by
    intro M N
    cases M with
    | var x =>
      cases N with
      | var x' =>
        intro h
        have := of_decide_eq_true h
        exact congrArg var this
      | app _ _ => intro h; contradiction
      | abs _ _ => intro h; contradiction

    | app P Q =>
      cases N with
      | app P' Q' =>
        intro h
        _
      | var _ => intro h; contradiction
      | abs _ _ => intro h; contradiction

    | abs x Q =>
      cases N with
      | abs x' Q' =>
        intro h
        _
      | var _ => intro h; contradiction
      | app _ _ => intro h; contradiction

  rfl := by
    intro M
    cases M with
    | var x => exact (beq_iff_eq ..).mpr rfl
    | app P Q => exact (beq_iff_eq ..).mpr rfl
    | abs x Q => exact (beq_iff_eq ..).mpr rfl

instance instDecidableInSub {M N : Λ} : Decidable (M ∈ Sub N) :=
  List.instDecidableMemOfLawfulBEq M (Sub N)

instance instDecidableSubterm {M N : Λ} : Decidable (Subterm M N) :=
  match M, N with
  | var x, var y =>
    if h : x = y
      then isTrue (by rw [h]; exact IsRefl.refl ..)
      else isFalse (by simp; exact h)
  | var x, app P Q =>
    if h : var x ∈ Sub P ∨ var x ∈ Sub Q
      then isTrue (by simp; exact h)
      else isFalse (by simp; rw [not_or] at h; exact h)
  | var x, abs y Q =>
    if h : var x ∈ Sub Q
      then isTrue (by simp; exact h)
      else isFalse (by simp; exact h)
  | app P Q, R =>
    if h : app P Q ∈ Sub R
      then isTrue (by simp; exact h)
      else isFalse (by simp; exact h)
  | abs x Q, R =>
    if h : abs x Q ∈ Sub R
      then isTrue (by simp; exact h)
      else isFalse (by simp; exact h)

-- 1.3.8: Proper subterm
@[simp] def ProperSubterm (L M : Λ) : Prop := L ⊆ M ∧ L ≠ M

@[simp] instance : HasSSubset Λ := ⟨ProperSubterm⟩

-- 1.4.1: The set of free variables of a λ-term
def FV : Λ → RBSet Name
| var x => .single x
| app M N => FV M ∪ FV N
| abs x M => FV M \ .single x

-- 1.4.3: Closed λ-term; combinator; Λ⁰
def Closed (M : Λ) : Prop := FV M = ∅

-- 1.5.1: Renaming; Mˣ ʸ; =ₐ
def rename (t : Λ) (x y : Name) : Λ :=
  match t with
  | var x' => if x' = x then var y else t
  | app M N => app (M.rename x y) (N.rename x y)
  | abs x' M => if x' ≠ x then abs x' (M.rename x y) else t

def isBound (x : Name) : Λ → Bool
| var _ => false
| app M N => isBound x M || isBound x N
| abs y M => x == y || isBound x M

inductive Renaming : Λ → Λ → Prop where
| rename {x y : Name} {M : Λ} : y ∉ (FV M) → ¬ isBound y M → Renaming (abs x M) (abs y (rename M x y))

-- 1.5.2: α-conversion or α-equivalence; =α
inductive AlphaEq : Λ → Λ → Prop where
| rename {M N : Λ} : Renaming M N → AlphaEq M N
| compatAppA {M N : Λ} : AlphaEq M N → AlphaEq (app M L) (app N L)
| compatAppB {M N : Λ} : AlphaEq M N → AlphaEq (app L M) (app L N)
| compatAbs {z : Name} {M N : Λ} : AlphaEq M N → AlphaEq (abs z M) (abs z N)
| refl (M : Λ) : AlphaEq M M
| symm {M N : Λ} : AlphaEq M N → AlphaEq N M
| trans {L M N : Λ} : AlphaEq L M → AlphaEq M N → AlphaEq L N

infix:50 " =α " => AlphaEq
macro_rules | `($x =α $y) => `(AlphaEq $x $y)

-- 1.6.1: Substitution
def subst (t : Λ) (x : Name) (N : Λ) : Λ :=
  match t with
  | var y => if x = y then N else t
  | app P Q => app (P.subst x N) (Q.subst x N)
  | abs y P => if (FV P).contains y then t else abs y (P.subst x N)

syntax term "[" term ":=" term "]" : term
macro_rules
| `($M[$x := $N]) => `(subst $M $x $N)

example (x y : Name) (L M N : Λ) (h : x ≠ y) (hxm : x ∉ FV L)
  : M[x := N][y := L] = M[y := L][y := N[y := L]] :=
  sorry

def reduceβ (t : Λ) : Λ :=
  match t with
  | app (abs x M) N => M[x := N]
  | app M N => app M.reduceβ N.reduceβ
  | abs y N => abs y N.reduceβ
  | var _ => t

syntax:1024 (name := betaReduction) "→β" term:1024 : term
macro_rules | `(→β$M) => `(Λ.reduceβ $M)

end Λ
