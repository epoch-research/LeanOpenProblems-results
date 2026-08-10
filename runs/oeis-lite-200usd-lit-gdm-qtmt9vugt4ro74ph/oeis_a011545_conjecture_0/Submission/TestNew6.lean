import FormalConjectures.Util.ProblemImports

open Real Int

lemma pi_div_arctan_gt (n : ℕ) (hn : 1 ≤ n) :
    Real.pi * (10 : ℝ)^n + 2 * (10 : ℝ)^(-(n + 2 : ℤ)) < Real.pi / Real.arctan (1 / (10 : ℝ)^n) := sorry

theorem test_arctan_lower :
  Real.pi * (10 : ℝ)^60 + 2 * (10 : ℝ)^(-(62 : ℤ)) < Real.pi / Real.arctan (1 / (10 : ℝ)^60) := by
  have h := pi_div_arctan_gt 60 (by norm_num)
  push_cast at h
  exact h
