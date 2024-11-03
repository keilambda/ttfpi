import Mathlib.Data.Multiset.Basic

universe u

abbrev Name := String

unsafe instance {α : Type u} [ToString α] : ToString (Multiset α) where
  toString s := toString (s.unquot.map toString)

inductive Star {α : Type u} (R : α → α → Prop) : α → α → Prop where
| zero (a : α) : Star R a a
| step {a b c : α} : R a b → Star R b c → Star R a c

namespace Star

variable {α b c : Type u}
variable {R : α → α → Prop}

@[refl]
theorem refl (a : α) : Star R a a := zero a

@[trans]
theorem trans {a b c : α} : Star R a b → Star R b c → Star R a c := by
  intro hlm hmn
  induction hlm with
  | zero => exact hmn
  | step hlm' _ IH => exact step hlm' (IH hmn)

end Star
