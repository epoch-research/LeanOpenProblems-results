import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_five : a 5 = 2976412336128 := by
  unfold a
  dsimp
  push_cast
  have h_target : Real.Gamma (9 * (5 : ℝ) + 1) * Real.Gamma (2 * (5 : ℝ) + 1) * Real.Gamma (3 / 2 * (5 : ℝ) + 1) /
    (Real.Gamma (9 / 2 * (5 : ℝ) + 1) * Real.Gamma (4 * (5 : ℝ) + 1) * Real.Gamma (3 * (5 : ℝ) + 1) * Real.Gamma ((5 : ℝ) + 1)) =
    Real.Gamma 46 * Real.Gamma 11 * Real.Gamma (17 / 2) / (Real.Gamma (47 / 2) * Real.Gamma 21 * Real.Gamma 16 * Real.Gamma 6) := by
    congr 2 <;> norm_num
  rw [h_target]
  -- We don't need to fully prove it, we just want to see if congr 2 <;> norm_num succeeds!
  sorry
