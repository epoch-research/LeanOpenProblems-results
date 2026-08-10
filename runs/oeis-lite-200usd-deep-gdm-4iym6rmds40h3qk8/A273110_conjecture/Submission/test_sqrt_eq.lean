import FormalConjectures.Util.ProblemImports

theorem test_sqrt_eq : Nat.sqrt 25 * Nat.sqrt 25 = 25 := by rfl
theorem test_sqrt_dec : Nat.sqrt 25 * Nat.sqrt 25 = 25 := by decide
