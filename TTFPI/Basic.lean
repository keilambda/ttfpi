import Batteries.Data.RBMap.Basic
import Mathlib.Data.Multiset.Basic

abbrev RBSet (α : Type u) [Ord α] := Batteries.RBSet α compare

@[inherit_doc] infix:50 " ≡ " => Eq
macro_rules | `($x ≡ $y) => `(binrel% Eq $x $y)

unsafe instance {α : Type u} [ToString α] : ToString (Multiset α) where
  toString s := toString (s.unquot.map toString)
