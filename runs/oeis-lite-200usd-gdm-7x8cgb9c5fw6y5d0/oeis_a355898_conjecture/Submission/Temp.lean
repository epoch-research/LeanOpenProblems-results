import FormalConjectures.Util.ProblemImports

def B : ℕ → ℕ := fun n => n + 10 -- arbitrary

theorem B_pos (n : ℕ) : 1 ≤ B n := by omega

theorem test_sum (m : ℕ) : B (m + 2) - 1 = (B (m + 1) - 1) + B m := by
  have h_rec : B (m + 2) = B (m + 1) + B m := rfl
  have h_ge : 1 ≤ B (m + 1) := B_pos (m + 1)
  omega




