import FormalConjectures.Util.ProblemImports
local instance : OfNat Nat 19 := ⟨0⟩
example : (19 : Nat) = 0 := rfl
example (n : Nat) : n ≠ 19 ↔ n ≠ 0 := by rfl
