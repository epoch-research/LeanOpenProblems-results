import Submission.Complete

open Real Nat Finset Filter Topology

lemma c1_gt_1 : 1 < exp (harmonic 1) * (exp (1 / 2 : ℝ) - 1) := by
  have H : (5:ℝ)/2 ≤ exp 1 := by
    have : (1:ℝ) = 1 := rfl
    have H2 := exp_lower_bound_7 1 (by positivity)
    linarith
  have H2 : 1 + 1/2 + 1/8 ≤ exp (1/2 : ℝ) := by
    have H3 := exp_lower_bound_7 (1/2) (by positivity)
    linarith
  have hh : (harmonic 1 : ℝ) = 1 := by norm_num
  rw [hh]
  calc
    1 = (5/2 : ℝ) * (13/8 - 1) - 9/16 := by norm_num
    _ < (5/2 : ℝ) * (13/8 - 1) := by linarith
    _ ≤ exp 1 * (1 + 1/2 + 1/8 - 1) := by
      apply mul_le_mul H (by linarith) (by norm_num) (exp_pos _).le
    _ ≤ exp 1 * (exp (1/2 : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le

lemma c_lt_2 (n : ℕ) (hn : 1 ≤ n) : exp (harmonic (n + 1)) - exp (harmonic n) < 2 := by
  by_cases h600 : n < 600
  · have h_le : exp (harmonic (n + 1)) - exp (harmonic n) ≤ exp (harmonic (600 + 1)) - exp (harmonic 600) := by
      have h_mono_c := c_mono_le (c := fun k => exp (harmonic (k + 1)) - exp (harmonic k)) ?_ n 600 hn h600.le
      · exact h_mono_c
      · intro k hk
        have h_k : exp (harmonic (k + 1)) - exp (harmonic k) ≤ exp (harmonic (k + 2)) - exp (harmonic (k + 1)) := by
          have h_eq1 : exp (harmonic (k + 1)) - exp (harmonic k) = exp (harmonic k) * (exp (1 / (k + 1 : ℝ)) - 1) := by
            have h1 : (harmonic (k + 1) : ℝ) = harmonic k + (k + 1 : ℝ)⁻¹ := by rw [harmonic_succ]; push_cast; rfl
            rw [h1, one_div, exp_add]; ring
          have h_eq2 : exp (harmonic (k + 2)) - exp (harmonic (k + 1)) = exp (harmonic (k + 1)) * (exp (1 / (k + 2 : ℝ)) - 1) := by
            have h2 : (harmonic (k + 1 + 1) : ℝ) = harmonic (k + 1) + (k + 2 : ℝ)⁻¹ := by
              rw [harmonic_succ]; push_cast; congr 1; ring
            rw [h2, one_div, exp_add]; ring
          rw [h_eq1, h_eq2]
          exact (c_mono k hk).le
        exact h_k
    have h_upper : exp (harmonic (600 + 1)) - exp (harmonic 600) < exp (harmonic (600 + 1)) / (600 + 1 : ℝ) := c_upper_bound 600
    have h_600 : exp (harmonic (600 + 1)) / (600 + 1 : ℝ) < exp (harmonic 600) / 600 := by
      have h_anti := exp_harmonic_div_n_anti 600 (by decide)
      exact_mod_cast h_anti
    have hc : exp (harmonic 600) / 600 < 2 := by
      have h_600_val := exp_harmonic_600_upper
      linarith
    linarith
  · push_neg at h600
    have h_upper : exp (harmonic (n + 1)) - exp (harmonic n) < exp (harmonic (n + 1)) / (n + 1 : ℝ) := c_upper_bound n
    have h_anti : exp (harmonic (n + 1)) / (n + 1 : ℝ) ≤ exp (harmonic 600) / 600 := by
      have h := exp_harmonic_div_n_le_600 (n + 1) (by omega)
      exact_mod_cast h
    have hc : exp (harmonic 600) / 600 < 2 := by
      have h_600_val := exp_harmonic_600_upper
      linarith
    linarith

lemma A206911_diff_eq_2_or_3 (n : ℕ) (hn : 1 ≤ n) : A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  dsimp [A206911_diff]
  rw [A206911_eq, A206911_eq]
  have h_bound : 1 < exp (harmonic (n + 1)) - 1 - (exp (harmonic n) - 1) ∧ exp (harmonic (n + 1)) - 1 - (exp (harmonic n) - 1) < 2 := by
    constructor
    · have hc_base : 1 < exp (harmonic 1) * (exp (1 / (1 + 1 : ℝ)) - 1) := by
        have h2 : ((1:ℝ) + 1) = 2 := by norm_num
        rw [h2]
        exact c1_gt_1
      have h_cn := c_mono_le (c := fun k => exp (harmonic k) * (exp (1 / ((k:ℝ) + 1)) - 1)) ?_ 1 n (by omega) hn
      · have h_harm : exp (harmonic n) * (exp (1 / ((n:ℝ) + 1)) - 1) = exp (harmonic (n + 1)) - exp (harmonic n) := by
          have h1 : (harmonic (n + 1) : ℝ) = harmonic n + ((n:ℝ) + 1)⁻¹ := by rw [harmonic_succ]; push_cast; rfl
          rw [h1, one_div, exp_add]
          ring
        have : exp (harmonic (n + 1)) - 1 - (exp (harmonic n) - 1) = exp (harmonic n) * (exp (1 / ((n:ℝ) + 1)) - 1) := by
          rw [h_harm]
          ring
        rw [this]
        have hc1 : ((1:ℕ):ℝ) = (1:ℝ) := by push_cast; rfl
        dsimp at h_cn
        rw [hc1] at h_cn
        exact hc_base.trans_le h_cn
      · intro k hk
        dsimp
        have h_k : exp (harmonic k) * (exp (1 / ((k:ℝ) + 1)) - 1) ≤ exp (harmonic (k + 1)) * (exp (1 / ((k:ℝ) + 1 + 1)) - 1) := by
          have h1 : ((k:ℝ) + 1 + 1) = (k + 2 : ℝ) := by ring
          rw [h1]
          have h_cast1 : (k:ℝ) + 1 = (k + 1 : ℝ) := by push_cast; rfl
          rw [h_cast1]
          exact (c_mono k hk).le
        have hc : ((k + 1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; rfl
        rw [hc]
        exact h_k
    · have hc2 : exp (harmonic (n + 1)) - exp (harmonic n) < 2 := c_lt_2 n hn
      linarith
  have h_pos1 : 0 ≤ exp (harmonic n) - 1 := by
    have : 1 ≤ exp (harmonic n) := by
      have h_zero : exp 0 ≤ exp (harmonic n) := Real.exp_monotone (harm_nonneg n)
      rwa [Real.exp_zero] at h_zero
    linarith
  have h_pos2 : 0 ≤ exp (harmonic (n + 1)) - 1 := by
    have : 1 ≤ exp (harmonic (n + 1)) := by
      have h_zero : exp 0 ≤ exp (harmonic (n + 1)) := Real.exp_monotone (harm_nonneg (n + 1))
      rwa [Real.exp_zero] at h_zero
    linarith
  have H := diff_eq_2_or_3 (x := exp (harmonic (n + 1)) - 1) (y := exp (harmonic n) - 1) h_pos1 h_pos2 h_bound
  have h_eq : (n + 1 + ⌊exp (harmonic (n + 1)) - 1⌋₊) - (n + ⌊exp (harmonic n) - 1⌋₊) = 1 + ⌊exp (harmonic (n + 1)) - 1⌋₊ - ⌊exp (harmonic n) - 1⌋₊ := by
    have h1 : (harmonic n : ℝ) ≤ (harmonic (n + 1) : ℝ) := by
      have h_succ : (harmonic (n + 1) : ℝ) = harmonic n + ((n:ℝ) + 1)⁻¹ := by rw [harmonic_succ]; push_cast; rfl
      rw [h_succ]
      exact le_add_of_nonneg_right (by positivity)
    have h2 : exp (harmonic n) - 1 ≤ exp (harmonic (n + 1)) - 1 := by
      have := Real.exp_monotone h1
      linarith
    have h3 : ⌊exp (harmonic n) - 1⌋ ≤ ⌊exp (harmonic (n + 1)) - 1⌋ := Int.floor_mono h2
    have h4 : ⌊exp (harmonic n) - 1⌋₊ ≤ ⌊exp (harmonic (n + 1)) - 1⌋₊ := Int.toNat_le_toNat h3
    omega
  rwa [h_eq]
