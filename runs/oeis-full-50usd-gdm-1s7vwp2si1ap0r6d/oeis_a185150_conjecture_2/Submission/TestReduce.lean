import FormalConjectures.Util.ProblemImports

-- Test if Nat.Prime is kernel reducible
theorem test_prime : Nat.Prime 3 := by decide

-- Test if jacobiSym is kernel reducible
theorem test_jacobi : jacobiSym (1 : ℤ) 3 = 1 := by decide
