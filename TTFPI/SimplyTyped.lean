/-
# Simply Typed λ-calculus: λ→
-/

abbrev Name := String

-- 2.2.1: The set Typ of all simple types
inductive Typ where
| var (α : Name)
| arrow (σ : Typ) (τ : Typ)
deriving Repr

namespace Typ

protected def toString : Typ → String
| var α => α
| arrow σ τ => "(" ++ σ.toString ++ " → " ++ τ.toString ++ ")"

instance : ToString Typ := ⟨Typ.toString⟩

end Typ

-- 2.4.1: Pre-typed λ-terms
inductive Term where
| var (name : Name)
| app (fn : Term) (arg : Term)
| abs (param : Name) (type : Typ) (body : Term)
deriving Repr

instance : Coe Name Term := ⟨Term.var⟩
