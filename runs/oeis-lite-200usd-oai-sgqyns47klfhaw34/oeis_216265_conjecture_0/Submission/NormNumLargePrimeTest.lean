import FormalConjectures.Util.ProblemImports
example : Nat.Prime 2741 := by norm_num
example : ¬ Nat.Prime 2197 := by norm_num
example : Nat.Prime 7993 := by norm_num
#print axioms NormNumLargePrimeTest._example_1
