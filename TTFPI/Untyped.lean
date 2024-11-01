import TTFPI.Basic

import Aesop
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Defs
import Mathlib.Order.RelClasses

/-!
# Untyped λ-calculus

Note that we are not using `simp` or `aesop` in this file, even though our code is written in a
style that is compatible with these tactics. This is because we want to keep the proofs as explicit
as possible, for educational purposes.
-/

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
def Sub (t : Λ) : Multiset Λ :=
  match t with
  | var _ => {t}
  | app M N => t ::ₘ (Sub M + Sub N)
  | abs _ M => t ::ₘ Sub M

@[simp]
def Subterm (L M : Λ) : Prop := L ∈ Sub M

@[simp]
instance : HasSubset Λ := ⟨Subterm⟩

-- 1.3.6
instance instIsReflInSub : IsRefl Λ (· ∈ Sub ·) where
  refl M := by
    induction M with
    | var _ => rw [Sub, Multiset.mem_singleton]
    | app P Q => rw [Sub]; exact Multiset.mem_cons_self ..
    | abs _ Q => rw [Sub]; exact Multiset.mem_cons_self ..

instance instIsReflSubterm : IsRefl Λ Subterm := inferInstanceAs (IsRefl Λ (· ∈ Sub ·))

instance instIsReflSubset : IsRefl Λ Subset := inferInstanceAs (IsRefl Λ (· ∈ Sub ·))

instance : IsTrans Λ (· ∈ Sub ·) where
  trans L M N hlm hmn := by
    induction N with
    | var _ =>
      rw [Sub, Multiset.mem_singleton]
      rw [Sub, Multiset.mem_singleton] at hmn
      rw [hmn] at hlm
      rw [Sub, Multiset.mem_singleton] at hlm
      assumption
    | app P Q hP hQ =>
      rw [Sub, Multiset.mem_cons, Multiset.mem_add]
      rw [Sub, Multiset.mem_cons, Multiset.mem_add] at hmn
      cases hmn with
      | inl h =>
        subst h
        rw [Sub, Multiset.mem_cons, Multiset.mem_add] at hlm
        assumption
      | inr h => cases h with
        | inl hl => exact Or.inr (Or.inl (hP hl))
        | inr hr => exact Or.inr (Or.inr (hQ hr))
    | abs _ Q hQ =>
      rw [Sub, Multiset.mem_cons]
      rw [Sub, Multiset.mem_cons] at hmn
      cases hmn with
      | inl h =>
        subst h
        rw [Sub, Multiset.mem_cons] at hlm
        assumption
      | inr h => exact Or.inr (hQ h)

instance : IsTrans Λ Subterm := inferInstanceAs (IsTrans Λ (· ∈ Sub ·))
instance : IsTrans Λ Subset := inferInstanceAs (IsTrans Λ (· ∈ Sub ·))

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
def FV : Λ → Finset Name
| var x => {x}
| app M N => FV M ∪ FV N
| abs x M => FV M \ {x}

-- 1.4.3: Closed λ-term; combinator; Λ⁰
def Closed (M : Λ) : Prop := M.FV.Nonempty

instance : Decidable (Closed M) := inferInstanceAs (Decidable M.FV.Nonempty)

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

@[aesop safe [constructors]]
inductive Renaming : Λ → Λ → Prop where
| rename (x y : Name) (M : Λ) (hfv : y ∉ (FV M)) (hnb : ¬ M.hasBindingVar y) : Renaming (abs x M) (abs y (rename M x y))

@[simp]
theorem renaming_rename {x y : Name} {M : Λ} {hfv : y ∉ (FV M)} {hnb : ¬ M.hasBindingVar y} : Renaming (abs x M) (abs y (rename M x y)) :=
  Renaming.rename x y M hfv hnb

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

instance : Coe (Renaming M N) (AlphaEq M N) := ⟨AlphaEq.rename⟩

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

theorem eq_imp_alpha_eq (h : M = N) : M =α N := by subst h; rfl

instance : IsRefl Λ (· =α ·) := ⟨AlphaEq.refl⟩
instance : IsSymm Λ (· =α ·) := ⟨@AlphaEq.symm⟩
instance : IsTrans Λ (· =α ·) := ⟨@AlphaEq.trans⟩

instance : Equivalence AlphaEq := ⟨AlphaEq.refl, AlphaEq.symm, AlphaEq.trans⟩

-- 1.6.1: Substitution
def gensym : StateM Nat Name := getModify Nat.succ <&> toString

def gensymNotIn (fv : Finset Name) : StateM Nat Name := do
  let mut y ← gensym
  while y ∈ fv do
    y ← gensym
  return y

def subst (t : Λ) (x : Name) (N : Λ) : StateM Nat Λ :=
  match t with
  | var y => pure $ if x = y then N else t
  | app P Q => app <$> P.subst x N <*> Q.subst x N
  | abs y P =>
    if x = y then
      pure t
    else if y ∈ N.FV then do
      let z ← gensymNotIn N.FV
      abs z <$> ((P.rename y z).subst x N)
    else
      abs y <$> (P.subst x N)
termination_by t.size
decreasing_by all_goals simp_wf <;> simp_arith

def subst' (t : Λ) (x : Name) (N : Λ) : Λ := t.subst x N |>.run' 0

syntax term "[" term ":=" term ("," term)? "]" : term
macro_rules
| `($M[$x := $N]) => `(subst' $M $x $N)
| `($M[$x := $N, $n]) => `(subst $M $x $N |>.run' $n)

syntax (name := simp_subst) "simp_subst" : tactic
macro_rules
| `(tactic| simp_subst) =>
  `(tactic| simp [subst', StateT.run, subst, pure, StateT.pure, Seq.seq, StateT.bind, StateT.map, Functor.map])

theorem subst_noop (h : x ∉ M.FV) : M[x := N] = M := by
  induction M with
  | var y =>
    simp_subst
    rw [FV, Finset.mem_singleton] at h
    intro hxy
    contradiction
  | app P Q ihP ihQ =>
    simp_subst
    rw [FV, Finset.mem_union, not_or] at h
    exact ⟨ihP h.left, sorry⟩
  | abs y Q ihQ =>
    simp_subst
    rw [FV] at h
    if hxy : x = y then
      simp [hxy, StateT.pure]
    else if hyn : y ∈ N.FV then
      simp [hxy, hyn, gensymNotIn, gensym, bind, StateT.bind, StateT.pure, pure, StateT.map]
      sorry
    else
      sorry

-- 1.6.5
lemma subst_sequence (h : x ≠ y) (hxm : x ∉ L.FV) : M[x := N][y := L] = M[y := L][x := N[y := L]] := by
  induction M with
  | var z =>
    simp_subst
    by_cases hxz : x = z
    · simp [hxz]
      by_cases hyz : y = z
      · subst hxz hyz; contradiction
      · simp [hyz]; simp_subst
    · by_cases hyz : y = z
      · simp [hxz, hyz]
        simp_subst
        unfold subst
        sorry
      · simp [hxz, hyz, subst]
  | app P Q hP hQ =>
    simp_subst
    sorry
  | abs z Q hQ =>
    simp_subst
    sorry

-- 1.8.1: One-step β-reduction; →β
def reduceβ (t : Λ) : Λ :=
  match t with
  | app (abs x M) N => M[x := N]
  | app M N => app M.reduceβ N.reduceβ
  | abs y N => abs y N.reduceβ
  | var _ => t

inductive Beta : Λ → Λ → Prop where
| redex {x : Name} (M N : Λ) : Beta (app (abs x M) N) (M[x := N])
| compatAppLeft {L M N : Λ} : Beta M N → Beta (app M L) (app N L)
| compatAppRight {L M N : Λ} : Beta M N → Beta (app L M) (app L N)
| compatAbs {x : Name} {M N : Λ} : Beta M N → Beta (abs x M) (abs x N)

infixl:50 " →β " => Beta
macro_rules | `($M →β $N) => `(binrel% Beta $M $N)

infixl:50 " ←β " => fun M N => Beta N M
macro_rules | `($M ←β $N) => `(binrel% Beta $N $M)

@[simp]
theorem beta_redex {x : Name} {M N : Λ} : Beta (app (abs x M) N) (M[x := N]) := Beta.redex M N

@[simp]
theorem beta_compat_app_left {L M N : Λ} (h : M →β N) : app M L →β app N L := Beta.compatAppLeft h

@[simp]
theorem beta_compat_app_right {L M N : Λ} (h : M →β N) : app L M →β app L N := Beta.compatAppRight h

@[simp]
theorem beta_compat_abs {x : Name} {M N : Λ} (h : M →β N) : abs x M →β abs x N := Beta.compatAbs h

-- 1.8.3: β-reduction (zero-or-more-step); ↠β
abbrev BetaStar := Star Beta

infixl:50 " ↠β " => BetaStar
macro_rules | `($M ↠β $N) => `(binrel% BetaStar $M $N)

infixl:50 " ↞β " => fun M N => BetaStar N M
macro_rules | `($M ↞β $N) => `(binrel% BetaStar $N $M)

-- 1.8.4: extension of →β, reflexivity and transitivity
theorem BetaStar.extension : M →β N → M ↠β N := by
  intro h
  exact Star.step h (Star.zero N)

instance : Coe (M →β N) (M ↠β N) := ⟨BetaStar.extension⟩

-- 1.8.5: β-conversion; β-equality; =β
@[aesop safe [constructors]]
inductive BetaEq : Λ → Λ → Prop where
| beta {M N : Λ} : Beta M N → BetaEq M N
| betaInv {M N : Λ} : Beta N M → BetaEq M N
| refl (M : Λ) : BetaEq M M
| symm {M N : Λ} : BetaEq M N → BetaEq N M
| trans {L M N : Λ} : BetaEq L M → BetaEq M N → BetaEq L N

infix:50 " =β " => BetaEq
macro_rules | `($M =β $N) => `(binrel% BetaEq $M $N)

@[simp]
theorem beta_eq_beta (h : M →β N) : M =β N := BetaEq.beta h

@[simp]
theorem beta_eq_beta_inv (h : M ←β N) : M =β N := BetaEq.betaInv h

@[refl]
theorem beta_eq_refl (M : Λ) : M =β M := BetaEq.refl M

@[symm]
theorem beta_eq_symm (h : M =β N) : N =β M := BetaEq.symm h

@[trans]
theorem beta_eq_trans (hlm : L =β M) (hmn : M =β N) : L =β N := BetaEq.trans hlm hmn

-- 1.8.6: extension of ↠β, reflexivity, symmetry and transitivity
theorem BetaEq.extension : M ↠β N → M =β N := by
  intro h
  induction h with
  | zero => rfl
  | step hlm _ IH => exact trans (beta hlm) IH

theorem BetaEq.extensionInv : M ↞β N → M =β N := by
  intro h
  induction h with
  | zero => rfl
  | step hlm _ IH => exact trans IH (betaInv hlm)

instance : IsRefl Λ (· =β ·) := ⟨BetaEq.refl⟩
instance : IsSymm Λ (· =β ·) := ⟨@BetaEq.symm⟩
instance : IsTrans Λ (· =β ·) := ⟨@BetaEq.trans⟩

instance : Equivalence BetaEq := ⟨BetaEq.refl, BetaEq.symm, BetaEq.trans⟩

-- 1.9.1: β-normal form; β-nf; β-normalizing
def isRedex : Λ → Prop
| app (abs _ _) _ => True
| _ => False

instance : Decidable (M.isRedex) :=
  match M with
  | var _ => isFalse (by rw [isRedex, not_false_eq_true]; trivial)
  | app (var _) _ => isFalse (by rw [isRedex, not_false_eq_true]; trivial)
  | app (app _ _) _ => isFalse (by rw [isRedex, not_false_eq_true]; trivial)
  | app (abs _ _) _ => isTrue (by rw [isRedex]; reduce; trivial)
  | abs _ _ => isFalse (by rw [isRedex, not_false_eq_true]; trivial)

def inNormalForm : Λ → Prop
| var _ => True
| app M N => ¬ isRedex (app M N) ∧ inNormalForm M ∧ inNormalForm N
| abs _ M => inNormalForm M

protected def hasDecIsNormalForm (M : Λ) : Decidable M.inNormalForm :=
  match M with
  | var _ => isTrue (by rw [inNormalForm]; trivial)
  | app M N =>
    if h : isRedex (app M N)
      then isFalse (by rw [inNormalForm, not_and]; intro nh; contradiction)
      else match M.hasDecIsNormalForm, N.hasDecIsNormalForm with
        | isFalse hM, _ => isFalse (by rw [inNormalForm, not_and, not_and]; intro _ nh; contradiction)
        | _, isFalse hN => isFalse (by rw [inNormalForm, not_and, not_and]; intro _ _ nh; contradiction)
        | isTrue hM, isTrue hN => isTrue (by rw [inNormalForm]; exact ⟨h, hM, hN⟩)
  | abs _ M => M.hasDecIsNormalForm

instance : Decidable (M.inNormalForm) := Λ.hasDecIsNormalForm M

def hasNormalForm (M : Λ) : Prop := ∃ N : Λ, N.inNormalForm ∧ M =β N

-- 1.9.2: α-equivalence implication
@[simp]
theorem nf_beta_imp_eq (h : M.inNormalForm) (hmn : M →β N) : M = N := by
  induction hmn with
  | redex M N =>
    rw [inNormalForm, isRedex] at h
    rw [not_true_eq_false, false_and] at h
    contradiction
  | @compatAppLeft L M N _ IH =>
    rw [inNormalForm, isRedex] at h
    exact congrFun (congrArg app (IH h.right.left)) L
  | @compatAppRight L M N _ IH =>
    rw [inNormalForm, isRedex] at h
    exact congrArg (app L) (IH h.right.right)
  | @compatAbs x M N _ IH =>
    rw [inNormalForm] at h
    exact congrArg (abs x) (IH h)

@[simp]
theorem nf_beta_star_imp_eq (h : M.inNormalForm) (hmn : M ↠β N) : M = N := by
  induction hmn with
  | zero => rfl
  | step hlm hmn IH => cases hmn <;> (have := nf_beta_imp_eq h hlm; subst this; exact IH h)

theorem nf_beta_star_imp_alpha_eq (h : M.inNormalForm) (hmn : M ↠β N) : M =α N :=
  eq_imp_alpha_eq (nf_beta_star_imp_eq h hmn)

-- 1.9.5: Reduction path
abbrev FiniteReductionPath := Star Beta

instance : IsRefl Λ FiniteReductionPath := ⟨@Star.refl _ _⟩
instance : IsTrans Λ FiniteReductionPath := ⟨@Star.trans _ _⟩

def isWeaklyNormalizing (M : Λ) : Prop := ∃ N : Λ, N.inNormalForm ∧ M ↠β N

def isStronglyNormalizing (M : Λ) : Prop := Acc Beta M

-- 1.10.1: Fixpoint
theorem fixpoint : ∀ L : Λ, ∃ M : Λ, app L M =β M := by
  intro L
  let U := lam "x" ↦ L :$ ("x" :$ "x")
  let M := U :$ U
  have h : M →β (L :$ M) := sorry
  exact ⟨M, .betaInv h⟩

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

def zero := lam "f", "x" ↦ "x"
def one := lam "f", "x" ↦ "f" :$ "x"
def two := lam "f", "x" ↦ "f" :$ ("f" :$ "x")
def three := lam "f", "x" ↦ "f" :$ ("f" :$ ("f" :$ "x"))

def add : Λ := lam "m", "n", "f", "x" ↦ "m" :$ "f" :$ ("n" :$ "f" :$ "x")
def mul : Λ := lam "m", "n", "f", "x" ↦ "m" :$ ("n" :$ "f") :$ "x"

def suc := lam "m", "f", "x" ↦ "f" :$ ("m" :$ "f" :$ "x")

def true := lam "x", "y" ↦ "x"
def false := lam "x", "y" ↦ "y"
def not := lam "z" ↦ "z" :$ false :$ true

end Combinators

end Λ
