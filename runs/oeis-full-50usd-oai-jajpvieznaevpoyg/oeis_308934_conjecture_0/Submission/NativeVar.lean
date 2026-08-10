import FormalConjectures.Util.ProblemImports
example (n : Nat) : n = n := by native_decide
example (n : Nat) : n ≤ n := by native_decide
example (n : Nat) : decide (n ≤ n) = true := by native_decide
#print axioms _example
