import FormalConjectures.Util.ProblemImports
example : ∀ n : ℕ, n = n := by
  classical
  exact of_decide_eq_true (by native_decide : decide (∀ n : ℕ, n = n) = true)
example : ∀ n : ℕ, n = n := by
  classical
  exact of_decide_eq_true (by rfl : decide (∀ n : ℕ, n = n) = true)
