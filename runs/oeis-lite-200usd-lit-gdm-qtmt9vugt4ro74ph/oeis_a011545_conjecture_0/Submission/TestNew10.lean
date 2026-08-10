import FormalConjectures.Util.ProblemImports

open Real Int

theorem test_change (k : ℤ) (h2 : (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ (60 + 0 + 1)))
    (h_ub : Real.pi / Real.arctan (1 / (10 : ℝ) ^ 61) < Real.pi * (10 : ℝ) ^ 61 + 2 * (10 : ℝ) ^ (-61 : ℤ)) :
    (k : ℝ) < Real.pi * (10 : ℝ) ^ 61 + 2 * (10 : ℝ) ^ (-61 : ℤ) := by
  change (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ 61) at h2
  exact lt_trans h2 h_ub
