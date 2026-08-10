import FormalConjectures.Util.ProblemImports

open Real Int

lemma pi_div_arctan_gt (n : ℕ) (hn : 1 ≤ n) :
    Real.pi * (10 : ℝ)^n + 2 * (10 : ℝ)^(-(n + 2 : ℤ)) < Real.pi / Real.arctan (1 / (10 : ℝ)^n) := sorry

theorem test_arctan_lower :
  Real.pi * (10 : ℝ)^60 + 2 * (0.01 * (10 : ℝ)^(-60 : ℤ)) < Real.pi / Real.arctan (1 / (10 : ℝ)^60) := by
  have h_arctan_lower := pi_div_arctan_gt 60 (by norm_num)
  push_cast at h_arctan_lower
  have h_pow_neg_eq : (10 : ℝ) ^ (-(62 : ℤ)) = 0.01 * (10 : ℝ) ^ (-60 : ℤ) := by
    have : (-(62 : ℤ)) = (-60 : ℤ) + (-2 : ℤ) := by omega
    rw [this, zpow_add₀ (by norm_num)]
    ring
  rw [h_pow_neg_eq] at h_arctan_lower
  exact h_arctan_lower
