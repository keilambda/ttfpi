import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

universe u

abbrev Name := String

unsafe instance {α : Type u} [ToString α] : ToString (Multiset α) where
  toString s := toString (s.unquot.map toString)

unsafe instance {α : Type u} [ToString α] : ToString (Finset α) where
  toString s := toString s.1
