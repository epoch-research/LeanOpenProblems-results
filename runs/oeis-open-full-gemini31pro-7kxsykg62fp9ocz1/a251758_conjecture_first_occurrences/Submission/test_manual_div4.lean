import Mathlib

theorem t1 : Nat.divisors (17 * 19) = {1, 17, 19, 323} := by
  have h1 : 17 * 19 = 323 := by rfl
  rw [h1]
  decide
