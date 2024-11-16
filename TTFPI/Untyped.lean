import TTFPI.Basic

import Aesop
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Logic.Relation
import Mathlib.Order.Defs
import Mathlib.Order.RelClasses

/-!
# Untyped λ-calculus

Note that we are not using `simp` or `aesop` in this file, even though our code is written in a
style that is compatible with these tactics. This is because we want to keep the proofs as explicit
as possible, for educational purposes.
-/

namespace Untyped

-- 1.3.2: The set Λ of all λ-terms
inductive Λ where
| var (name : Name)
| app (fn : Λ) (arg : Λ)
| abs (param : Name) (body : Λ)
deriving Repr, Ord, DecidableEq

namespace Λ
open Relation (ReflTransGen)

variable {L M N P Q R : Λ}
variable {x y z u v w : Name}

protected def toString : Λ → String
| var name => name
| app M N => s!"({M.toString} {N.toString})"
| abs x M => s!"(λ{x}. {M.toString})"

instance : ToString Λ := ⟨Λ.toString⟩

instance : Coe Name Λ := ⟨var⟩

syntax "lam" term,+ "↦" term : term
macro_rules
| `(lam $x ↦ $M) => `(abs $x $M)
| `(lam $x, $xs,* ↦ $M) => do
  let N ← `(lam $xs,* ↦ $M)
  `(abs $x $N)

infixl:100 " ∙ " => app

@[simp]
def size : Λ → Nat
| var _ => 1
| app M N => 1 + M.size + N.size
| abs _ N => 1 + N.size

instance : SizeOf Λ := ⟨size⟩

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
instance : IsRefl Λ (· ∈ Sub ·) where
  refl M := by
    induction M with
    | var _ => rw [Sub, Multiset.mem_singleton]
    | app P Q => rw [Sub]; exact Multiset.mem_cons_self ..
    | abs _ Q => rw [Sub]; exact Multiset.mem_cons_self ..

instance : IsRefl Λ Subterm := inferInstanceAs (IsRefl Λ (· ∈ Sub ·))

instance : IsRefl Λ Subset := inferInstanceAs (IsRefl Λ (· ∈ Sub ·))

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
def Closed (M : Λ) : Prop := M.FV = ∅

instance : Decidable M.Closed := inferInstanceAs (Decidable (M.FV = ∅))

-- 1.5.1: Renaming; Mˣ ʸ; =ₐ
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
    match P.hasDecHasBindingVar x, Q.hasDecHasBindingVar x with
    | isTrue hP, _ => isTrue (by exact Or.inl hP)
    | _, isTrue hQ => isTrue (by exact Or.inr hQ)
    | isFalse hP, isFalse hQ => isFalse (by rw [hasBindingVar, not_or]; exact ⟨hP, hQ⟩)
  | abs y Q =>
    if h : x = y
      then isTrue (by rw [hasBindingVar]; exact Or.inl h)
      else
        match Q.hasDecHasBindingVar x with
        | isTrue hQ => isTrue (by exact Or.inr hQ)
        | isFalse hQ => isFalse (by rw [hasBindingVar, not_or]; exact ⟨h, hQ⟩)

instance : Decidable (M.hasBindingVar x) := M.hasDecHasBindingVar x

@[simp]
def rename (t : Λ) (x y : Name) : Λ :=
  match t with
  | var x' => if x' = x then var y else t
  | app M N => app (M.rename x y) (N.rename x y)
  | abs x' M =>
    if M.hasBindingVar y ∨ y ∈ M.FV then t
    else if x' = x then abs y (M.rename x y)
    else abs x' (M.rename x y)

@[simp]
theorem rename_size_eq : (M.rename x y).size = M.size := by
  induction M with
  | var _ => rw [rename, size]; split <;> rw [size]
  | app P Q hP hQ => rw [rename, size, hP, hQ, size]
  | abs _ Q hQ =>
    rw [rename, size]
    split
    · rw [size]
    next h => rw [not_or] at h; split <;> (next hx => simp [hx, hQ])

example : (lam "x" ↦ "x").rename "x" "y" = lam "y" ↦ "y" := rfl
example : (lam "x" ↦ "y").rename "x" "y" = lam "x" ↦ "y" := rfl
example : (lam "x", "y" ↦ "x").rename "x" "y" = lam "x", "y" ↦ "x" := rfl

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
theorem alpha_eq_rename : Renaming M N → AlphaEq M N := AlphaEq.rename

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

theorem eq_imp_alpha_eq (h : M = N) : M =α N := by rw [h]

instance : IsRefl Λ (· =α ·) := ⟨AlphaEq.refl⟩
instance : IsSymm Λ (· =α ·) := ⟨@AlphaEq.symm⟩
instance : IsTrans Λ (· =α ·) := ⟨@AlphaEq.trans⟩

instance : Equivalence AlphaEq := ⟨AlphaEq.refl, AlphaEq.symm, AlphaEq.trans⟩

-- 1.5.4: α-variant
abbrev AlphaVariant := AlphaEq

-- 1.6.1: Substitution
def gensym : StateM Nat Name := getModify Nat.succ <&> toString

def gensymNotIn (fv : Finset Name) : StateM Nat Name := do
  let mut y ← gensym
  while y ∈ fv do
    y ← gensym
  return y

def substGensym (t : Λ) (x : Name) (N : Λ) : StateM Nat Λ :=
  match t with
  | var y => pure $ if x = y then N else t
  | app P Q => app <$> P.substGensym x N <*> Q.substGensym x N
  | abs y P =>
    if x = y then
      pure t
    else if y ∈ N.FV then do
      let z ← gensymNotIn N.FV
      abs z <$> ((P.rename y z).substGensym x N)
    else
      abs y <$> (P.substGensym x N)
termination_by t.size
decreasing_by all_goals simp_wf <;> simp_arith

def substGensym' (t : Λ) (x : Name) (N : Λ) : Λ := t.substGensym x N |>.run' 0

def subst (t : Λ) (x : Name) (N : Λ) : Λ :=
  match t with
  | var y => if x = y then N else t
  | app P Q => app (P.subst x N) (Q.subst x N)
  | abs y P => if x = y ∨ y ∈ N.FV then t else abs y (P.subst x N)

syntax term "[" term ":=" term ("," term)? "]" : term
macro_rules
| `($M[$x := $N]) => `(subst $M $x $N)

theorem subst_noop (h : x ∉ M.FV) : M.subst x N = M := by
  induction M with
  | var y =>
    rw [subst]
    rw [FV, Finset.mem_singleton] at h
    exact if_neg h
  | app P Q ihP ihQ =>
    rw [FV, Finset.mem_union, not_or] at h
    rw [subst, app.injEq]
    exact ⟨ihP h.left, ihQ h.right⟩
  | abs y P ihP =>
    rw [FV] at h
    rw [subst]
    if hxy : x = y then
      simp [hxy]
    else
      rw [Finset.mem_sdiff, Finset.mem_singleton] at h
      simp [hxy] at h
      simp [hxy]
      exact (fun _ => ihP h)

-- 1.6.5
lemma subst_sequence (h : x ≠ y) (hxm : x ∉ L.FV) : M[x := N][y := L] = M[y := L][x := N[y := L]] := by
  induction M with
  | var z =>
    by_cases hxz : x = z
    · simp [hxz]
      by_cases hyz : y = z
      · subst hxz hyz; contradiction
      · simp [hyz, subst]
    · by_cases hyz : y = z
      · simp [hxz, hyz, subst, subst_noop hxm]
      · simp [hxz, hyz, subst]
  | app P Q hP hQ => simp [subst, hP, hQ]
  | abs z Q hQ =>
    simp [subst, hQ]
    by_cases hxz : x = z
    · by_cases hyz : y = z
      · subst hxz hyz; contradiction
      · simp_all [subst]
    · sorry

-- 1.7.1: modulo α-equivalence
-- NOTE: take a look at errata
lemma modulo_alpha_eq_app (hmn : M =α N) (hpq : P =α Q) : M ∙ P =α N ∙ Q := sorry

lemma modulo_alpha_eq_abs (h : M =α N) : abs x M =α abs x N := sorry

lemma modulo_alpha_eq_subst (hmn : M =α N) (hpq : P =α Q) : M[x := P] =α N[x := Q] := sorry

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
abbrev BetaChain := ReflTransGen Beta

infixl:50 " ↠β " => BetaChain
macro_rules | `($M ↠β $N) => `(binrel% BetaChain $M $N)

infixl:50 " ↞β " => fun M N => BetaChain N M
macro_rules | `($M ↞β $N) => `(binrel% BetaChain $N $M)

-- 1.8.4: extension of →β, reflexivity and transitivity
theorem BetaChain.extension : M →β N → M ↠β N := ReflTransGen.single

instance : Coe (M →β N) (M ↠β N) := ⟨BetaChain.extension⟩

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

theorem eq_imp_beta_eq (h : M = N) : M =β N := by rw [h]

-- 1.8.6: extension of ↠β, reflexivity, symmetry and transitivity
theorem BetaEq.extension : M ↠β N → M =β N := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hbc IH => exact trans IH (beta hbc)

theorem BetaEq.extensionInv : M ↞β N → M =β N := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hbc IH => exact trans (betaInv hbc) IH

instance : IsRefl Λ (· =β ·) := ⟨BetaEq.refl⟩
instance : IsSymm Λ (· =β ·) := ⟨@BetaEq.symm⟩
instance : IsTrans Λ (· =β ·) := ⟨@BetaEq.trans⟩

instance : Equivalence BetaEq := ⟨BetaEq.refl, BetaEq.symm, BetaEq.trans⟩

-- 1.9.1: β-normal form; β-nf; β-normalizing
def Redex : Λ → Prop
| app (abs _ _) _ => True
| _ => False

instance : Decidable M.Redex :=
  match M with
  | var _ => isFalse (by dsimp [Redex]; trivial)
  | app (var _) _ => isFalse (by dsimp [Redex]; trivial)
  | app (app _ _) _ => isFalse (by dsimp [Redex]; trivial)
  | app (abs _ _) _ => isTrue (by rw [Redex]; trivial)
  | abs _ _ => isFalse (by dsimp [Redex]; trivial)

def InNormalForm : Λ → Prop
| var _ => True
| app M N => ¬ Redex (app M N) ∧ InNormalForm M ∧ InNormalForm N
| abs _ M => InNormalForm M

protected def hasDecInNormalForm (M : Λ) : Decidable M.InNormalForm :=
  match M with
  | var _ => isTrue (by rw [InNormalForm]; trivial)
  | app M N =>
    if h : Redex (app M N)
      then isFalse (by rw [InNormalForm, not_and]; intro nh; contradiction)
      else match M.hasDecInNormalForm, N.hasDecInNormalForm with
        | isFalse hM, _ => isFalse (by rw [InNormalForm, not_and, not_and]; intro _ nh; contradiction)
        | _, isFalse hN => isFalse (by rw [InNormalForm, not_and, not_and]; intro _ _ nh; contradiction)
        | isTrue hM, isTrue hN => isTrue (by rw [InNormalForm]; exact ⟨h, hM, hN⟩)
  | abs _ M => M.hasDecInNormalForm

instance : Decidable M.InNormalForm := M.hasDecInNormalForm

def hasNormalForm (M : Λ) : Prop := ∃ N : Λ, N.InNormalForm ∧ M =β N

def reduceβAll (t : Λ) : Λ := loop t t.size
  where loop : Λ → Nat → Λ
  | t, 0 => t
  | t, n + 1 =>
    let r := reduceβ t
    if r.InNormalForm then r
    else loop r n

-- 1.9.2: α-equivalence implication
@[simp]
theorem nf_beta_imp_eq (h : M.InNormalForm) (hmn : M →β N) : M = N := by
  induction hmn with
  | redex M N =>
    rw [InNormalForm, Redex] at h
    rw [not_true_eq_false, false_and] at h
    contradiction
  | @compatAppLeft L M N _ IH =>
    exact congrFun (congrArg app (IH h.right.left)) L
  | @compatAppRight L M N _ IH =>
    exact congrArg (app L) (IH h.right.right)
  | @compatAbs x M N _ IH =>
    exact congrArg (abs x) (IH h)

@[simp]
theorem nf_beta_chain_imp_eq (h : M.InNormalForm) (hmn : M ↠β N) : M = N := by
  induction hmn with
  | refl => rfl
  | tail hlm hmn IH =>
    cases hlm
    · exact nf_beta_imp_eq h hmn
    · subst IH; exact nf_beta_imp_eq h hmn

theorem nf_beta_chain_imp_alpha_eq (h : M.InNormalForm) (hmn : M ↠β N) : M =α N :=
  eq_imp_alpha_eq (nf_beta_chain_imp_eq h hmn)

-- 1.9.5: Reduction path
abbrev FiniteReductionPath := ReflTransGen Beta

instance : IsRefl Λ FiniteReductionPath := ⟨@ReflTransGen.refl _ _⟩
instance : IsTrans Λ FiniteReductionPath := ⟨@ReflTransGen.trans _ _⟩

-- 1.9.6: Weak normalization, strong normalization
def WeaklyNormalizing (M : Λ) : Prop := ∃ N : Λ, N.InNormalForm ∧ M ↠β N

def StronglyNormalizing (M : Λ) : Prop := Acc Beta M

-- 1.9.8: Church-Rosser; CR; Confluence
theorem church_rosser {L M N : Λ} (hmn : L ↠β M) (hmp : L ↠β N) : ∃ P : Λ, M ↠β P ∧ N ↠β P :=
  Relation.church_rosser (fun hl hm hn hlhm hlhn => sorry) hmn hmp

-- 1.9.9: Church-Rosser Corollary
theorem church_rosser_corollary {L M N : Λ} (hmn : M =β N) : ∃ L : Λ, M ↠β L ∧ N ↠β L := by
  induction hmn with
  | beta hmn => sorry
  | betaInv _ => sorry
  | refl hmn => exact ⟨hmn, by rw [and_self]⟩
  | symm hmn ih => obtain ⟨_, h⟩ := ih; exact ⟨_, h.symm⟩
  | trans _ => sorry

-- 1.10.1: Fixpoint
theorem fixpoint {x : Name} (L : Λ) (h : x ∉ L.FV) : ∃ M : Λ, app L M =β M := by
  let U := lam x ↦ L ∙ (x ∙ x)
  let M := U ∙ U
  have : M →β (L ∙ (x ∙ x)).subst x U := Beta.redex ..
  simp [subst, subst_noop h] at this
  exact ⟨M, .betaInv this⟩

def toNat? : Λ → Option Nat
| abs _ (abs _ t) =>
  let rec loop (e : Λ) : Option Nat :=
    match e with
    | var _ => some 0
    | app (var _) e' =>
        match loop e' with
        | some n => some (n + 1)
        | none => none
    | _ => none
  loop t
| _ => none

def toNat! (M : Λ) : Nat := M.toNat?.getD default

def toBool? : Λ → Option Bool
| abs x (abs y (var z)) => if x = z then some true else if y = z then some false else none
| _ => none

def toBool! (M : Λ) : Bool := M.toBool?.getD default

namespace Combinators

def Ω := (lam "x" ↦ "x" ∙ "x") ∙ (lam "x" ↦ "x" ∙ "x")
def Δ := lam "x" ↦ "x" ∙ "x" ∙ "x"
def Y := lam "f" ↦ (lam "x" ↦ "f" ∙ ("x" ∙ "x")) ∙ (lam "x" ↦ "f" ∙ ("x" ∙ "x"))

-- SKI
def S := lam "x", "y", "z" ↦ ("x" ∙ "z") ∙ ("y" ∙ "z")
def K := lam "x", "y" ↦ "x"
def I := lam "x" ↦ "x"

-- BCKW
def B := lam "x", "y", "z" ↦ "x" ∙ ("y" ∙ "z")
def C := lam "x", "y", "z" ↦ "x" ∙ "z" ∙ "y"
def W := lam "x", "y" ↦ "x" ∙ "y" ∙ "y"

def zero := lam "f", "x" ↦ "x"
def one := lam "f", "x" ↦ "f" ∙ "x"
def two := lam "f", "x" ↦ "f" ∙ ("f" ∙ "x")
def three := lam "f", "x" ↦ "f" ∙ ("f" ∙ ("f" ∙ "x"))

def add : Λ := lam "m", "n", "f", "x" ↦ "m" ∙ "f" ∙ ("n" ∙ "f" ∙ "x")
def mul : Λ := lam "m", "n", "f", "x" ↦ "m" ∙ ("n" ∙ "f") ∙ "x"

def suc := lam "m", "f", "x" ↦ "f" ∙ ("m" ∙ "f" ∙ "x")

def true := lam "x", "y" ↦ "x"
def false := lam "x", "y" ↦ "y"
def not := lam "z" ↦ "z" ∙ false ∙ true

end Combinators
end Λ
end Untyped
