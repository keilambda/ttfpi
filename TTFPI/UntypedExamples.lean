import TTFPI.Untyped

import Aesop
import Batteries.Data.RBMap.Lemmas

open Λ

def I : Λ := lam "y" ↦ "y"

open Batteries in
theorem renamingI : Renaming Combinators.I I := by
  constructor
  · simp [FV, (· ∈ ·), RBSet.Mem, RBSet.MemP, RBNode.MemP, compare, compareOfLessAndEq]
  · simp

example : AlphaEq Combinators.I I :=
  AlphaEq.rename renamingI

def x2y := lam "x" ↦ "y"
#eval x2y.rename "y" "z"

def ex : Λ := lam "x" ↦ ("x" :$ "y")
#eval ex.subst' "y" I |> toString
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

#eval Λ.subst' M "x" "y" |> toString
#eval Λ.subst' M "z" "y" |> toString
#eval Λ.reduceβ M
