import Batteries.Data.RBMap.Basic

abbrev RBSet (α : Type u) [Ord α] := Batteries.RBSet α compare

@[inherit_doc] infix:50 " ≡ " => Eq
macro_rules | `($x ≡ $y) => `(binrel% Eq $x $y)
