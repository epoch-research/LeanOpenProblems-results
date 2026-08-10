import FormalConjectures.Util.ProblemImports

open Real

theorem test_n_4 : (5 : ℝ) < (4 : ℝ) ^ ((4 : ℝ) ^ (1 / (4 : ℝ))) := by
  -- We know (4 : ℝ) ^ (1 / 4) = 2 ^ (2 / 4) = 2 ^ (1 / 2) = Real.sqrt 2
  -- Let's prove 1.4 < (4 : ℝ) ^ (1 / (4 : ℝ))
  -- Since 1.4 = 7 / 5, we can show (7/5)^4 < 4
  have h1 : (7 / 5 : ℝ) ^ (4 : ℝ) < 4 := by
    have h_pow : (7 / 5 : ℝ) ^ (4 : ℝ) = (7 / 5 : ℝ) ^ (4 : ℕ) := rpow_natCast (7 / 5) 4
    rw [h_pow]
    norm_num
  have h2 : (7 / 5 : ℝ) < (4 : ℝ) ^ (1 / (4 : ℝ)) := by
    have h_pos : 0 ≤ (7 / 5 : ℝ) := by norm_num
    rw [← rpow_lt_rpow_iff h_pos (by positivity : 0 ≤ (4 : ℝ) ^ (1 / (4 : ℝ))) (by norm_num : 0 < (4 : ℝ))]
    have h_mul : (1 / (4 : ℝ)) * 4 = 1 := by norm_num
    have h_pow4 : ((4 : ℝ) ^ (1 / (4 : ℝ))) ^ (4 : ℝ) = 4 := by
      rw [← rpow_mul (by norm_num : 0 ≤ (4 : ℝ))]
      rw [h_mul, rpow_one]
    rw [h_pow4]
    exact h1
  have h3 : (5 : ℝ) < (4 : ℝ) ^ (7 / 5 : ℝ) := by
    have h5_pow : (5 : ℝ) ^ (5 : ℝ) = (5 : ℝ) ^ (5 : ℕ) := rpow_natCast 5 5
    have h4_pow : ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (5 : ℝ) = (4 : ℝ) ^ (7 : ℝ) := by
      rw [← rpow_mul (by norm_num : 0 ≤ (4 : ℝ))]
      have h_mul2 : (7 / 5 : ℝ) * 5 = 7 := by norm_num
      rw [h_mul2]
    have h4_pow_nat : (4 : ℝ) ^ (7 : ℝ) = (4 : ℝ) ^ (7 : ℕ) := rpow_natCast 4 7
    have h_lt_pow5 : (5 : ℝ) ^ (5 : ℝ) < ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (5 : ℝ) := by
      rw [h5_pow, h4_pow, h4_pow_nat]
      norm_num
    have h_base_pos : 0 ≤ (5 : ℝ) := by norm_num
    rw [rpow_lt_rpow_iff h_base_pos (by positivity : 0 ≤ ((4 : ℝ) ^ (7 / 5 : ℝ))) (by norm_num : 0 < (5 : ℝ))] at h_lt_pow5
    exact h_lt_pow5
  have h_final : (4 : ℝ) ^ (7 / 5 : ℝ) < (4 : ℝ) ^ ((4 : ℝ) ^ (1 / (4 : ℝ))) := by
    apply rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (4 : ℝ))
    exact h2
  exact lt_trans h3 h_final
