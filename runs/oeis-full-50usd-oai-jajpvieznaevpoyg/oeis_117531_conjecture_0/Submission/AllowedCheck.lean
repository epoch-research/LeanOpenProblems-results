import FormalConjectures.Util.ProblemImports
example : (2 : Nat) + 2 = 4 := by native_decide
#print axioms _example
example : (2 : Nat) + 2 = 4 := by decide
#print axioms _example_1
