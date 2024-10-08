import TTFPI.Basic

import Aesop
import Batteries.Data.RBMap.Lemmas
import Mathlib.Order.Defs
import Mathlib.Order.RelClasses

-- 1.3.2: The set Λ of all λ-terms
abbrev Name := String

inductive Λ where
| var : Name → Λ
| app : Λ → Λ → Λ
| abs : Name → Λ → Λ
deriving Repr, Ord, DecidableEq

namespace Λ

variable {L M N P Q R : Λ}
variable {x y z u v w : Name}

protected def toString : Λ → String
| var name => name
| app M N => s!"({Λ.toString M} {Λ.toString N})"
| abs x M => s!"(λ{x}. {Λ.toString M})"

instance : ToString Λ := ⟨Λ.toString⟩

instance : Coe Name Λ := ⟨Λ.var⟩

syntax "lam" term,+ "↦" term : term
macro_rules
| `(lam $x ↦ $M) => `(Λ.abs $x $M)
| `(lam $x, $xs,* ↦ $M) => do
  let N ← `(lam $xs,* ↦ $M)
  `(Λ.abs $x $N)

infixl:100 " :$ " => Λ.app

@[simp]
def size : Λ → Nat
| var _ => 1
| app M N => 1 + M.size + N.size
| abs _ N => 1 + N.size

instance : SizeOf Λ := ⟨Λ.size⟩

-- 1.3.5: Multiset of subterms
@[simp]
def Sub (t : Λ) : List Λ :=
  match t with
  | var _ => [t]
  | app M N => t :: (Sub M ++ Sub N)
  | abs _ M => t :: Sub M

@[simp]
def Subterm (L M : Λ) : Prop := L ∈ Sub M

@[simp]
instance : HasSubset Λ := ⟨Subterm⟩

-- 1.3.6
@[simp]
instance instIsReflInSub : IsRefl Λ (· ∈ Sub ·) where
  refl M := by
    induction M with
    | var _ => rw [Sub, List.mem_singleton]
    | app P Q => rw [Sub]; exact List.mem_cons_self ..
    | abs _ Q => rw [Sub]; exact List.mem_cons_self ..

@[simp]
instance instIsReflSubterm : IsRefl Λ Subterm := inferInstanceAs (IsRefl Λ (· ∈ Sub ·))

@[simp]
instance instIsReflSubset : IsRefl Λ Subset := inferInstanceAs (IsRefl Λ (· ∈ Sub ·))

@[simp]
instance : IsTrans Λ (· ∈ Sub ·) where
  trans L M N hlm hmn := by
    induction N with
    | var _ =>
      rw [Sub, List.mem_singleton]
      rw [Sub, List.mem_singleton] at hmn
      rw [hmn] at hlm
      rw [Sub, List.mem_singleton] at hlm
      assumption
    | app P Q hP hQ =>
      rw [Sub, List.mem_cons, List.mem_append]
      rw [Sub, List.mem_cons, List.mem_append] at hmn
      cases hmn with
      | inl h =>
        subst h
        rw [Sub, List.mem_cons, List.mem_append] at hlm
        assumption
      | inr h => cases h with
        | inl hl => exact Or.inr (Or.inl (hP hl))
        | inr hr => exact Or.inr (Or.inr (hQ hr))
    | abs _ Q hQ =>
      rw [Sub, List.mem_cons]
      rw [Sub, List.mem_cons] at hmn
      cases hmn with
      | inl h =>
        subst h
        rw [Sub, List.mem_cons] at hlm
        assumption
      | inr h => exact Or.inr (hQ h)

instance : IsTrans Λ Subterm := inferInstanceAs (IsTrans Λ (· ∈ Sub ·))

instance : IsTrans Λ Subset := inferInstanceAs (IsTrans Λ (· ∈ Sub ·))

instance : Decidable (M ∈ Sub N) := List.instDecidableMemOfLawfulBEq M (Sub N)

instance : Decidable (Subterm M N) := inferInstanceAs (Decidable (M ∈ Sub N))

instance : Decidable (Subset M N) := inferInstanceAs (Decidable (M ∈ Sub N))

-- 1.3.8: Proper subterm
@[simp]
def ProperSubterm (L M : Λ) : Prop := L ≠ M ∧ L ⊆ M

@[simp]
instance : HasSSubset Λ := ⟨ProperSubterm⟩

instance : Decidable (ProperSubterm M N) := inferInstanceAs (Decidable (M ≠ N ∧ M ⊆ N))

instance : Decidable (M ⊂ N) := inferInstanceAs (Decidable (M ≠ N ∧ M ⊆ N))

-- 1.4.1: The set of free variables of a λ-term
def FV : Λ → RBSet Name
| var x => .single x
| app M N => FV M ∪ FV N
| abs x M => FV M \ .single x

-- 1.4.3: Closed λ-term; combinator; Λ⁰
def Closed (M : Λ) : Prop := M.FV.isEmpty

instance : Decidable (Closed M) := inferInstanceAs (Decidable M.FV.isEmpty)

-- 1.5.1: Renaming; Mˣ ʸ; =ₐ
@[simp]
def rename (t : Λ) (x y : Name) : Λ :=
  match t with
  | var x' => if x' = x then var y else t
  | app M N => app (M.rename x y) (N.rename x y)
  | abs x' M => if x = x' then t else abs x' (M.rename x y)

@[simp]
theorem rename_size_eq : (M.rename x y).size = M.size := by
  induction M with
  | var _ => rw [rename, size]; split <;> rw [size]
  | app P Q hP hQ => rw [rename, size, hP, hQ, size]
  | abs _ Q hQ =>
    rw [rename, size]
    split
    · rw [size]
    · rw [size, hQ]

@[simp]
def hasBindingVar (t : Λ) (x : Name) : Prop :=
  match t with
  | var _ => False
  | app M N => M.hasBindingVar x ∨ N.hasBindingVar x
  | abs y N => x = y ∨ N.hasBindingVar x

protected def hasDecHasBindingVar (M : Λ) (x : Name) : Decidable (M.hasBindingVar x) :=
  match M with
  | var _ => isFalse (by rw [hasBindingVar, not_false_eq_true]; trivial)
  | app P Q =>
    match Λ.hasDecHasBindingVar P x, Λ.hasDecHasBindingVar Q x with
    | isTrue hP, _ => isTrue (by exact Or.inl hP)
    | _, isTrue hQ => isTrue (by exact Or.inr hQ)
    | isFalse hP, isFalse hQ => isFalse (by rw [hasBindingVar, not_or]; exact ⟨hP, hQ⟩)
  | abs y Q =>
    if h : x = y
      then isTrue (by rw [hasBindingVar]; exact Or.inl h)
      else
        match Λ.hasDecHasBindingVar Q x with
        | isTrue hQ => isTrue (by exact Or.inr hQ)
        | isFalse hQ => isFalse (by rw [hasBindingVar, not_or]; exact ⟨h, hQ⟩)

instance : Decidable (M.hasBindingVar x) := Λ.hasDecHasBindingVar M x

inductive Renaming : Λ → Λ → Prop where
| rename {x y : Name} {M : Λ} : y ∉ (FV M) → ¬ M.hasBindingVar y → Renaming (abs x M) (abs y (rename M x y))

-- 1.5.2: α-conversion or α-equivalence; =α
@[aesop safe [constructors]]
inductive AlphaEq : Λ → Λ → Prop where
| rename {M N : Λ} : Renaming M N → AlphaEq M N
| compatAppLeft {L M N : Λ} : AlphaEq M N → AlphaEq (app M L) (app N L)
| compatAppRight {L M N : Λ} : AlphaEq M N → AlphaEq (app L M) (app L N)
| compatAbs {z : Name} {M N : Λ} : AlphaEq M N → AlphaEq (abs z M) (abs z N)
| refl (M : Λ) : AlphaEq M M
| symm {M N : Λ} : AlphaEq M N → AlphaEq N M
| trans {L M N : Λ} : AlphaEq L M → AlphaEq M N → AlphaEq L N

infix:50 " =α " => AlphaEq
macro_rules | `($x =α $y) => `(binrel% AlphaEq $x $y)

@[simp]
theorem alpha_eq_compat_app_left (h : M =α N) : app M L =α app N L := AlphaEq.compatAppLeft h

@[simp]
theorem alpha_eq_compat_app_right (h : M =α N) : app L M =α app L N := AlphaEq.compatAppRight h

@[simp]
theorem alpha_eq_compat_abs (h : M =α N) : abs z M =α abs z N := AlphaEq.compatAbs h

@[refl]
theorem alpha_eq_refl (M : Λ) : M =α M := AlphaEq.refl M

@[symm]
theorem alpha_eq_symm (h : M =α N) : N =α M := AlphaEq.symm h

@[trans]
theorem alpha_eq_trans (hlm : L =α M) (hmn : M =α N) : L =α N := AlphaEq.trans hlm hmn

instance : IsRefl Λ (· =α ·) := ⟨AlphaEq.refl⟩

instance : IsSymm Λ (· =α ·) := ⟨@AlphaEq.symm⟩

instance : IsTrans Λ (· =α ·) := ⟨@AlphaEq.trans⟩

instance : Equivalence AlphaEq := ⟨AlphaEq.refl, AlphaEq.symm, AlphaEq.trans⟩

-- 1.6.1: Substitution
def subst (t : Λ) (x : Name) (N : Λ) : StateM Nat Λ :=
  match t with
  | var y => pure $ if x = y then N else t
  | app P Q => app <$> P.subst x N <*> Q.subst x N
  | abs y P =>
    if y = x then
      pure t
    else if y ∈ N.FV then do
      let y' ← gensym
      let P' := P.rename y y'
      abs y' <$> (P'.subst x N)
    else
      abs y <$> (P.subst x N)
termination_by t.size
decreasing_by all_goals simp_wf <;> simp_arith
where
  gensym : StateM Nat Name := getModify Nat.succ <&> toString

def subst' (t : Λ) (x : Name) (N : Λ) : Λ := t.subst x N |>.run' 0

syntax term "[" term ":=" term ("," term)? "]" : term
macro_rules
| `($M[$x := $N]) => `(subst' $M $x $N)
| `($M[$x := $N, $n]) => `(subst $M $x $N |>.run' $n)

-- 1.6.5
lemma subst_sequence (h : x ≠ y) (hxm : x ∉ L.FV) : M[x := N][y := L] = M[y := L][x := N[y := L]] := by
  induction M with
  | var z =>
    simp [subst, subst', StateT.run]
    by_cases hxz : x = z
    · simp [hxz]
      by_cases hyz : y = z
      · subst hxz hyz; aesop
      · simp [pure, StateT.pure, hyz, subst]
    · simp [pure, StateT.pure]
      by_cases hyz : y = z
      · simp [hxz, hyz, subst, pure, StateT.pure]
        sorry
      · simp [hxz, hyz, subst]
  | app P Q hP hQ =>
    simp [subst, subst', StateT.run]
    sorry
  | abs z Q hQ =>
    simp [subst, subst', StateT.run]
    sorry

def reduceβ (t : Λ) : Λ :=
  match t with
  | app (abs x M) N => M[x := N]
  | app M N => app M.reduceβ N.reduceβ
  | abs y N => abs y N.reduceβ
  | var _ => t

syntax:1024 (name := betaReduction) "→β" term:1024 : term
macro_rules | `(→β$M) => `(Λ.reduceβ $M)

namespace Combinators

def Ω := (lam "x" ↦ "x" :$ "x") :$ (lam "x" ↦ "x" :$ "x")
def Δ := lam "x" ↦ "x" :$ "x" :$ "x"
def Y := lam "f" ↦ (lam "x" ↦ "f" :$ ("x" :$ "x")) :$ (lam "x" ↦ "f" :$ ("x" :$ "x"))

-- SKI
def S := lam "x", "y", "z" ↦ ("x" :$ "z") :$ ("y" :$ "z")
def K := lam "x", "y" ↦ "x"
def I := lam "x" ↦ "x"

-- BCKW
def B := lam "x", "y", "z" ↦ "x" :$ ("y" :$ "z")
def C := lam "x", "y", "z" ↦ "x" :$ "z" :$ "y"
def W := lam "x", "y" ↦ "x" :$ "y" :$ "y"

end Combinators

end Λ
