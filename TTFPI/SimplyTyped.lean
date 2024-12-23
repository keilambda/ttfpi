import TTFPI.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Relation
import Mathlib.Order.Heyting.Basic

/-
# Simply Typed λ-calculus: λ→
-/

namespace SimplyTyped

-- 2.2.1: The set Typ of all simple types
inductive Typ where
| var (α : Name)
| arrow (σ : Typ) (τ : Typ)
deriving Repr, DecidableEq

namespace Typ

protected def toString : Typ → String
| var α => α
| arrow σ τ => s!"{σ.toString} → {τ.toString}"

instance : ToString Typ := ⟨Typ.toString⟩

instance : Coe Name Typ := ⟨var⟩

infixr:20 " ⇒ " => arrow

end Typ

-- 2.4.1: Pre-typed λ-terms
inductive Term where
| var (name : Name)
| app (fn : Term) (arg : Term)
| abs (param : Name) (type : Typ) (body : Term)
deriving Repr, DecidableEq

namespace Term

variable {M N : Term}

protected def toString : Term → String
| var name => name
| app M N => s!"({M.toString} {N.toString})"
| abs x σ M => s!"(λ{x} : {σ}. {M.toString})"

instance : ToString Term := ⟨Term.toString⟩

instance : Coe Name Term := ⟨var⟩

infixl:100 " ∙ " => app

@[simp]
def Sub (L : Term) : Multiset Term :=
  match L with
  | var _ => {L}
  | app M N => L ::ₘ (Sub M + Sub N)
  | abs _ _ M => L ::ₘ Sub M

@[simp]
def Subterm (L M : Term) : Prop := L ∈ Sub M

@[simp]
instance : HasSubset Term := ⟨Subterm⟩

instance : Decidable (Subterm M N) := inferInstanceAs (Decidable (M ∈ Sub N))
instance : Decidable (Subset M N) := inferInstanceAs (Decidable (M ∈ Sub N))

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
| var {Γ : Context} {x : Name} {σ : Typ} :
    (x, σ) ∈ Γ →
    Judgement Γ x σ
| app {Γ : Context} {M N : Term} {σ τ : Typ} :
    Judgement Γ M (σ ⇒ τ) →
    Judgement Γ N σ →
    Judgement Γ (M ∙ N) τ
| abs {Γ : Context} {x : Name} {M : Term} {σ τ : Typ} :
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
  | @var _ _ α h =>
    simp [Term.FV, dom]
    exact ⟨α, h⟩
  | app jM jN ihM ihN =>
    simp [Term.FV]
    apply Finset.union_subset
    · exact ihM
    · exact ihN
  | abs Δ' ihM =>
    simp [Term.FV]
    simp [dom_insert_eq_insert_dom] at ihM
    exact Finset.diff_subset_iff.mpr ihM

-- 2.10.5: Thinning, Condensing, Permutation
@[simp]
theorem thinning {Γ Δ : Context} {M : Term} {σ : Typ} (h : Γ ⊆ Δ) : (Γ ⊢ M : σ) → (Δ ⊢ M : σ) := by
  intro J
  induction J with
  | var h' => exact Judgement.var (h h')
  | app jP jQ ihP ihQ => exact Judgement.app (ihP h) (ihQ h)
  | abs Δ' ih =>
    apply Judgement.abs
    sorry

@[simp]
theorem condensing {Γ : Context} {M : Term} {σ : Typ} (J : Γ ⊢ M : σ) : (Γ ↾ M.FV) ⊢ M : σ := by
  induction J with
  | var h =>
    apply Judgement.var
    simp [Term.FV]
    sorry
  | app jP jQ ihP ihQ =>
    apply Judgement.app
    simp [Term.FV]
    · sorry
    · sorry
    · sorry
  | abs Δ' ih =>
    apply Judgement.abs
    simp [Term.FV]
    sorry

@[simp]
theorem permutation {Γ Δ : Context} {M : Term} {σ : Typ} (h : Permutation Γ Δ) : (Γ ⊢ M : σ) → (Δ ⊢ M : σ) := by
  intro J
  induction J with
  | var h' =>
    apply Judgement.var
    sorry
  | app jP jQ ihP ihQ => exact Judgement.app (ihP h) (ihQ h)
  | abs Θ ih =>
    apply Judgement.abs
    sorry

-- 2.10.7: Generation Lemma
@[simp]
theorem generation_var {Γ : Context} {x : Name} {σ : Typ} : (Γ ⊢ x : σ) ↔ (x, σ) ∈ Γ := by
  apply Iff.intro
  · intro h; cases h; assumption
  · apply Judgement.var

@[simp]
theorem generation_app {Γ : Context} {M N : Term} {τ : Typ} : (Γ ⊢ M ∙ N : τ) ↔ (∃ σ : Typ, (Γ ⊢ M : σ ⇒ τ) ∧ (Γ ⊢ N : σ)) := by
  apply Iff.intro
  · intro h; cases h; case mp.app σ hn hm => exact ⟨σ, ⟨hm, hn⟩⟩
  · intro h; cases h; case mpr.intro σ h => exact Judgement.app h.left h.right

@[simp]
theorem generation_abs {Γ : Context} {x : Name} {M : Term} {σ ρ : Typ} : (Γ ⊢ Term.abs x σ M : ρ) ↔ (∃ τ : Typ, ((insert (x, σ) Γ) ⊢ M : τ) ∧ ρ = (σ ⇒ τ)) := by
  apply Iff.intro
  · intro h; cases h; case mp.abs τ h => exact ⟨τ, ⟨h, rfl⟩⟩
  · intro h; cases h; case mpr.intro τ h => rw [h.right]; exact Judgement.abs h.left

-- 2.10.8: Subterm Lemma
theorem subterm {M : Term} (h : Legal M) : ∀ N, N ⊆ M → Legal N := by
  intro N hN
  cases h with
  | intro Γ h =>
    obtain ⟨ρ, J⟩ := h
    induction J with
    | @var Δ x α h =>
      simp at hN
      subst hN
      exact ⟨Δ, α, Judgement.var h⟩
    | @app Δ P Q α β jP jQ ihP ihQ =>
      simp [Legal]
      simp at hN
      cases hN with
      | inl h => subst h; exact ⟨Δ, β, Judgement.app jP jQ⟩
      | inr h => cases h with
        | inl h => simp at ihP; exact ihP h
        | inr h => simp at ihQ; exact ihQ h
    | @abs Δ x P α β Δ' ih =>
      simp [Legal]
      simp at hN
      cases hN with
      | inl h => subst h; exact ⟨Δ, (α ⇒ β), Judgement.abs Δ'⟩
      | inr h => simp at ih; exact ih h

-- 2.10.9: Uniqueness of Types
@[simp]
theorem uniqueness_of_types {Γ : Context} {M : Term} {σ τ : Typ} (Jσ : Γ ⊢ M : σ) (Jτ : Γ ⊢ M : τ) : σ = τ := by
  induction M with
  | var x => sorry
  | app P Q ihP ihQ => sorry
  | abs x ρ M ih => sorry

-- 2.10.10: Decidability of Well-typedness, Type Assignment, Type Checking and Term Finding
@[simp]
def WellTyped (M : Term) : Prop := ∃ σ, ⊢ M : σ

@[simp]
def TypeAssignment (Γ : Context) (M : Term) : Prop := ∃ σ, Γ ⊢ M : σ

@[simp]
def TypeChecking (Γ : Context) (M : Term) (σ : Typ) : Prop := Γ ⊢ M : σ

@[simp]
def TermFinding (Γ : Context) (σ : Typ) : Prop := ∃ M, Γ ⊢ M : σ

def hasDecTypeable (M : Term) : Decidable (Typeable M) :=
  match M with
  | .var x => by
    simp only [Typeable, Statement]
    let σ : Typ := "σ"
    let Γ : Context := {(x, σ)}
    exact isTrue ⟨σ, Γ, by apply Judgement.var; rw [Finset.mem_singleton]⟩
  | .app P Q => by
    match hasDecTypeable P, hasDecTypeable Q with
    | isTrue tP, isTrue tQ =>
      simp only [Typeable, Statement] at *
      match P with
      | .var x =>
        let σ : Typ := "σ"
        let τ : Typ := "τ"
        let Γ : Context := {(x, σ ⇒ τ)}
        match Q with
        | .var y => exact isTrue ⟨τ, insert (y, σ) Γ, Judgement.app (by aesop) (by aesop)⟩
        | .app R S => sorry
        | .abs y ρ N => sorry
      | .app R S => sorry
      | .abs x ρ M => sorry
    | isFalse tP, _ => sorry
    | _, isFalse tQ => sorry
  | .abs x ρ P => by
    match hasDecTypeable P with
    | isTrue tP =>
      simp [Typeable, Statement] at *
      let σ : Typ := "σ"
      let Γ : Context := {(x, ρ)}
      sorry
    | isFalse ntP =>
      simp [Typeable, Statement] at ntP
      sorry

def hasDecWellTyped (M : Term) : Decidable (WellTyped M) := hasDecTypeable M

def hasDecTypeAssignment (Γ : Context) (M : Term) : Decidable (TypeAssignment Γ M) := sorry

def hasDecTypeChecking (Γ : Context) (M : Term) (σ : Typ) : Decidable (TypeChecking Γ M σ) :=
  match M with
  | .var x => by
    if h : (x, σ) ∈ Γ then
      exact isTrue (Judgement.var h)
    else
      dsimp
      rw [generation_var]
      exact isFalse (fun nh => by contradiction)
  | .app P Q => by
    match hasDecTypeChecking Γ P (σ ⇒ σ), hasDecTypeChecking Γ Q σ with
    | isTrue jP, isTrue jQ => exact isTrue (Judgement.app jP jQ)
    | isFalse njP, isTrue jQ =>
      dsimp at *
      simp [generation_app] at *
      exact isFalse (fun nh => by
        obtain ⟨ty, tyP, tyQ⟩ := nh
        have := uniqueness_of_types jQ tyQ
        subst this
        contradiction
      )
    | isTrue jP, isFalse njQ =>
      dsimp at *
      simp [generation_app] at *
      exact isFalse (fun nh => by
        obtain ⟨ty, tyP, tyQ⟩ := nh
        have := uniqueness_of_types jP tyP
        simp [Typ.arrow.injEq] at this
        subst this
        contradiction
      )
    | isFalse njP, isFalse njQ =>
      dsimp at *
      simp [generation_app] at *
      sorry
  | .abs x ρ P => by
    dsimp
    let τ : Typ := "τ"
    match hasDecTypeChecking (insert (x, ρ) Γ) P τ with
    | isTrue jP =>
      simp at *
      have := Judgement.abs jP
      have := generation_abs.mp this
      sorry
    | isFalse njP => sorry

def hasDecTermFinding (Γ : Context) (σ : Typ) : Decidable (TermFinding Γ σ) := sorry

instance {M : Term} : Decidable (Typeable M) := hasDecTypeable M
instance {M : Term} : Decidable (WellTyped M) := hasDecWellTyped M
instance {Γ : Context} {M : Term} : Decidable (TypeAssignment Γ M) := hasDecTypeAssignment Γ M
instance {Γ : Context} {M : Term} {σ : Typ} : Decidable (TypeChecking Γ M σ) := hasDecTypeChecking Γ M σ
instance {Γ : Context} {σ : Typ} : Decidable (TermFinding Γ σ) := hasDecTermFinding Γ σ

-- 2.11.1: Substitution Lemma
def subst (M : Term) (x : Name) (N : Term) : Term :=
  match M with
  | .var y => if x = y then N else M
  | .app P Q => .app (subst P x N) (subst Q x N)
  | .abs y σ P => if x = y ∨ y ∈ N.FV then M else .abs y σ (subst P x N)

syntax term "[" term ":=" term ("," term)? "]" : term
macro_rules
| `($M[$x := $N]) => `(subst $M $x $N)

theorem substitution {Γ Δ : Context} {M N : Term} {x : Name} {σ τ : Typ}
  (hM : insert (x, σ) (Γ ∪ Δ) ⊢ M : τ)
  (hN : Γ ⊢ N : σ)
  : (Γ ∪ Δ) ⊢ M[x := N] : τ := by
  sorry

-- 2.11.2: One-step β-reduction
def reduceβ : Term → Term
| .app (.abs x _ M) N => M[x := N]
| .var x => .var x
| .app M N => .app (reduceβ M) (reduceβ N)
| .abs x σ M => .abs x σ (reduceβ M)

inductive Beta : Term → Term → Prop where
| redex {x : Name} {σ : Typ} (M N : Term) : Beta (.app (.abs x σ M) N) (M[x := N])
| compatAppLeft {L M N : Term} : Beta M N → Beta (.app M L) (.app N L)
| compatAppRight {L M N : Term} : Beta M N → Beta (.app L M) (.app L N)
| compatAbs {x : Name} {σ : Typ} {M N : Term} : Beta M N → Beta (.abs x σ M) (.abs x σ N)

infixl:50 " →β " => Beta
macro_rules | `($M →β $N) => `(binrel% Beta $M $N)

infixl:50 " ←β " => fun M N => Beta N M
macro_rules | `($M ←β $N) => `(binrel% Beta $N $M)

@[simp]
theorem beta_redex {x : Name} {σ : Typ} {M N : Term} : Beta (.app (.abs x σ M) N) (M[x := N]) := Beta.redex M N

@[simp]
theorem beta_compat_app_left {L M N : Term} (h : M →β N) : .app M L →β .app N L := Beta.compatAppLeft h

@[simp]
theorem beta_compat_app_right {L M N : Term} (h : M →β N) : .app L M →β .app L N := Beta.compatAppRight h

@[simp]
theorem beta_compat_abs {x : Name} {σ : Typ} {M N : Term} (h : M →β N) : .abs x σ M →β .abs x σ N := Beta.compatAbs h

open Relation (ReflTransGen)
abbrev BetaChain := ReflTransGen Beta

infixl:50 " ↠β " => BetaChain
macro_rules | `($M ↠β $N) => `(binrel% BetaChain $M $N)

infixl:50 " ↞β " => fun M N => BetaChain N M
macro_rules | `($M ↞β $N) => `(binrel% BetaChain $N $M)

theorem BetaChain.extension {M N : Term} : M →β N → M ↠β N := ReflTransGen.single

instance {M N : Term} : Coe (M →β N) (M ↠β N) := ⟨BetaChain.extension⟩

@[aesop safe [constructors]]
inductive BetaEq : Term → Term → Prop where
| beta {M N : Term} : Beta M N → BetaEq M N
| betaInv {M N : Term} : Beta N M → BetaEq M N
| refl (M : Term) : BetaEq M M
| symm {M N : Term} : BetaEq M N → BetaEq N M
| trans {L M N : Term} : BetaEq L M → BetaEq M N → BetaEq L N

infix:50 " =β " => BetaEq
macro_rules | `($M =β $N) => `(binrel% BetaEq $M $N)

@[simp]
theorem beta_eq_beta {M N : Term} (h : M →β N) : M =β N := BetaEq.beta h

@[simp]
theorem beta_eq_beta_inv {M N : Term} (h : M ←β N) : M =β N := BetaEq.betaInv h

@[refl]
theorem beta_eq_refl (M : Term) : M =β M := BetaEq.refl M

@[symm]
theorem beta_eq_symm {M N : Term} (h : M =β N) : N =β M := BetaEq.symm h

@[trans]
theorem beta_eq_trans {L M N : Term} (hlm : L =β M) (hmn : M =β N) : L =β N := BetaEq.trans hlm hmn

theorem eq_imp_beta_eq {M N : Term} (h : M = N) : M =β N := by rw [h]

theorem BetaEq.extension {M N : Term} : M ↠β N → M =β N := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hbc IH => exact trans IH (beta hbc)

theorem BetaEq.extensionInv {M N : Term} : M ↞β N → M =β N := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hbc IH => exact trans (betaInv hbc) IH

instance : IsRefl Term (· =β ·) := ⟨BetaEq.refl⟩
instance : IsSymm Term (· =β ·) := ⟨@BetaEq.symm⟩
instance : IsTrans Term (· =β ·) := ⟨@BetaEq.trans⟩

instance : Equivalence BetaEq := ⟨BetaEq.refl, BetaEq.symm, BetaEq.trans⟩

-- 2.11.3: Church-Rosser Theorem; CR; Confluence
theorem church_rosser {L M N : Term} (hmn : L ↠β M) (hmp : L ↠β N) : ∃ P : Term, M ↠β P ∧ N ↠β P :=
  Relation.church_rosser (fun hl hm hn hlhm hlhn => sorry) hmn hmp

-- 2.11.4: CR Corollary
theorem church_rosser_corollary {M N : Term} (h : M =β N) : ∃ L : Term, M ↠β L ∧ N ↠β L :=
  sorry

-- 2.11.5: Subject reduction
theorem subject_reduction {Γ : Context} {L L' : Term} {ρ : Typ} (hj : Γ ⊢ L : ρ) (hb : L ↠β L') : Γ ⊢ L' : ρ :=
  sorry

-- 2.11.6: Strong normalization of legal terms
def StronglyNormalizing (M : Term) : Prop := Acc Beta M

theorem Legal_imp_StronglyNormalizing {M : Term} : Legal M → StronglyNormalizing M := sorry

end SimplyTyped
