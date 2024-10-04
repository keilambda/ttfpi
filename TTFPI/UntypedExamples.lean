import TTFPI.Untyped

import Aesop
import Batteries.Data.RBMap.Lemmas

open Λ

def I : Λ := lam "x" ↦ "x"
def I2 : Λ := lam "y" ↦ "y"

open Batteries in
theorem IdentityRenaming : Renaming I I2 := by
  have foo : ¬ ("y" ∈ FV "x") := by
    simp [FV, Membership.mem, RBSet.Mem, RBSet.MemP, RBNode.MemP, RBNode.Any, compare, compareOfLessAndEq]
  have bar : ¬ (isBound "y" "x") := by
    simp [isBound]
  exact (.rename foo bar)

def x2y := lam "x" ↦ "y"
#eval x2y.rename "y" "z"

-- example (hr : Renaming Rex (Rex.rename "y" "z")) : "z" ∈ FV (Rex.rename "y" "z") := by
--   simp [FV, (·∈·), Batteries.RBSet.Mem, Batteries.RBSet.MemP, Batteries.RBNode.MemP, Batteries.RBNode.Any, compare, compareOfLessAndEq]
--   cases hr with
--   | rename _ => sorry

def ex : Λ := lam "x" ↦ ("x" :$ "y")
#eval ex.subst "y" I |> toString
#eval ex["y" := I] |> toString
#eval (I :$ "x").reduceβ |> toString
#eval →β(I :$ "x")

#eval Sub ex |> toString
#eval (var "x") ⊆ ex
#eval (var "x") ⊂ ex
#eval FV ex
#eval "y" ∈ (FV ex)
#eval FV $ "x" :$ (lam "x" ↦ "x" :$ "y")
#eval Closed I
#eval ex.rename "x" "a" |>.rename "x" "b" |> toString

def M := (lam "x" ↦ "y") :$ "z"
#eval M.toString

#eval Λ.subst M "x" "y" |> toString
#eval Λ.subst M "z" "y" |> toString
#eval Λ.reduceβ M
