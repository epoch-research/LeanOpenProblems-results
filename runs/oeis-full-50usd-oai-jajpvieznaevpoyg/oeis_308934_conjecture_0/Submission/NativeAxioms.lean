import FormalConjectures.Util.ProblemImports
example : (2 : Nat) + 2 = 4 := by native_decide
theorem test_native : (2 : Nat) + 2 = 4 := by native_decide
#print axioms test_native
