import FormalConjectures.Util.ProblemImports
theorem finiteTrue : (1000 : Nat) + 1 = 1001 := by native_decide
#print axioms finiteTrue
theorem finiteTrue2 : (1000 : Nat) + 1 = 1001 := by decide
#print axioms finiteTrue2
