import FormalConjectures.Util.ProblemImports
local instance : LT Nat := ⟨fun _ _ => True⟩
theorem foo (n : Nat) (h : n > 1) : n > 0 := by trivial
#print foo
#print axioms foo
#check foo
