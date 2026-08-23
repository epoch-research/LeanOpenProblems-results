import FormalConjectures.Util.ProblemImports

lemma two_mul_div_le_log_one_add {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) / (2 * n + 1) ≤ Real.log (1 + 1 / n) := by
  have hx : (0 : ℝ) ≤ 1 / n := by positivity
  have h := Real.le_log_one_add_of_nonneg hx
  have : (2 : ℝ) * (1 / n) / (1 / n + 2) = 2 / (2 * n + 1) := by
    field_simp
    ring
  rwa [this] at h

lemma one_add_inv_pow_succ_ge_exp {n : ℕ} (hn : 0 < n) :
    Real.exp 1 ≤ ((n + 1 : ℝ) / n) ^ (n + 1) := by
  have hlog : (1 : ℝ) ≤ (n + 1 : ℝ) * Real.log (1 + 1 / n) := by
    have h1 := two_mul_div_le_log_one_add hn
    have h2 : (1 : ℝ) / (n + 1) ≤ 2 / (2 * n + 1) := by
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hn2 : (0 : ℝ) < 2 * n + 1 := by positivity
      rw [div_le_div_iff₀ hn1 hn2]
      norm_cast; omega
    have h3 : (1 : ℝ) ≤ (n + 1) * (2 / (2 * n + 1)) := by
      field_simp
      norm_cast; omega
    nlinarith
  have hpos : (0 : ℝ) < 1 + 1 / n := by positivity
  have hexp : Real.exp 1 ≤ Real.exp ((n + 1 : ℝ) * Real.log (1 + 1 / n)) :=
    Real.exp_le_exp.mpr hlog
  have hmul : Real.exp ((n + 1 : ℝ) * Real.log (1 + 1 / n)) =
      (1 + 1 / n) ^ (n + 1) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hpos]
    norm_cast
  have hfrac : (1 : ℝ) + 1 / n = (n + 1) / n := by field_simp
  rwa [hmul, hfrac] at hexp

lemma n_pow_mul_exp_le (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (n + 1) * Real.exp 1 ≤ (n + 1 : ℝ) ^ (n + 1) := by
  have hexp := one_add_inv_pow_succ_ge_exp hn
  have hmul := mul_le_mul_of_nonneg_right hexp
    (pow_nonneg (Nat.cast_nonneg n) (n + 1))
  have hrew : ((n + 1 : ℝ) / n) ^ (n + 1) * (n : ℝ) ^ (n + 1) =
      (n + 1 : ℝ) ^ (n + 1) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ this.ne'
  rw [hrew] at hmul
  linarith

lemma factorial_le_mul_exp_pow (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ (n : ℝ) * Real.exp 1 * ((n : ℝ) / Real.exp 1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => simp [Nat.factorial]
  | succ n hn ih =>
    have hn0 : 0 < n := by omega
    rw [Nat.factorial_succ]
    push_cast
    refine le_trans (mul_le_mul_of_nonneg_left ih (by positivity)) ?_
    have hpos_e : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hpow := n_pow_mul_exp_le n hn0
    have hL : (n + 1 : ℝ) * (n * Real.exp 1 * ((n : ℝ) / Real.exp 1) ^ n) =
        (n + 1) * Real.exp 1 * ((n : ℝ) ^ (n + 1) / Real.exp 1 ^ n) := by
      rw [div_pow, pow_succ']
      field_simp
    have hR : (n + 1 : ℝ) * Real.exp 1 * ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1) =
        (n + 1) * Real.exp 1 * ((n + 1 : ℝ) ^ (n + 1) / Real.exp 1 ^ (n + 1)) := by
      rw [div_pow]
    rw [hL, hR]
    have hpos1 : (0 : ℝ) < (n + 1 : ℝ) * Real.exp 1 := by positivity
    refine (mul_le_mul_iff_of_pos_left hpos1).mpr ?_
    rw [div_le_div_iff₀ (pow_pos hpos_e n) (pow_pos hpos_e _)]
    calc
      (n : ℝ) ^ (n + 1) * Real.exp 1 ^ (n + 1)
          = (n : ℝ) ^ (n + 1) * Real.exp 1 * Real.exp 1 ^ n := by
            rw [pow_succ]; ring
      _ ≤ (n + 1 : ℝ) ^ (n + 1) * Real.exp 1 ^ n :=
            mul_le_mul_of_nonneg_right hpow (pow_nonneg (le_of_lt hpos_e) _)
