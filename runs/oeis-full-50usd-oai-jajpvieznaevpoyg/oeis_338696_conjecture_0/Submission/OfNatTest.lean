import FormalConjectures.Util.ProblemImports
local instance : OfNat Nat 19 := ⟨0⟩
#eval (19 : Nat)
example (n : Nat) : n ≠ 19 ↔ n ≠ 0 := by simp
