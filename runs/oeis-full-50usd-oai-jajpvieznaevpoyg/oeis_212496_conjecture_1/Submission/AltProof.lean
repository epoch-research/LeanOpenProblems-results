import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real
noncomputable def b (n : ℕ) : ℝ := -2 / sqrt (n : ℝ)

lemma exp_half_lt_nine_fifths : Real.exp ((1:ℝ)/2) < (9:ℝ)/5 := by
  have h := Real.exp_bound' (x := (1:ℝ)/2) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  norm_num at h ⊢
  linarith

lemma exp_exp_two_lt_2009_aux : Real.exp (Real.exp 2) < (2009 : ℝ) := by
  have hE : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hEpos : 0 ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
  have hE2pow : Real.exp 1 ^ 2 < (2.7182818286 : ℝ) ^ 2 := pow_lt_pow_left₀ hE hEpos (by norm_num)
  have hexp2 : Real.exp 2 < (15 : ℝ) / 2 := by
    rw [show (2:ℝ) = (2:ℕ) * (1:ℝ) by norm_num, Real.exp_nat_mul]
    norm_num at hE2pow ⊢
    linarith
  have hE7pow : Real.exp 1 ^ 7 < (2.7182818286 : ℝ) ^ 7 := pow_lt_pow_left₀ hE hEpos (by norm_num)
  have hexp7 : Real.exp 7 < (1100 : ℝ) := by
    rw [show (7:ℝ) = (7:ℕ) * (1:ℝ) by norm_num, Real.exp_nat_mul]
    norm_num at hE7pow ⊢
    linarith
  have hexp75 : Real.exp ((15:ℝ)/2) < (2009 : ℝ) := by
    rw [show (15:ℝ)/2 = 7 + (1:ℝ)/2 by norm_num, Real.exp_add]
    nlinarith [hexp7, exp_half_lt_nine_fifths, Real.exp_pos 7, Real.exp_pos ((1:ℝ)/2)]
  exact lt_trans (Real.exp_strictMono hexp2) hexp75


theorem test (n : ℕ) :
  (n > 0 → b n < 0) ∧
  (n > 1 → b n < -1 / sqrt (n : ℝ)) ∧
  (n > 2008 → b n > -log (log (n : ℝ)) / sqrt (n : ℝ)) := by
  constructor
  · intro hn
    unfold b
    have hs : 0 < sqrt (n : ℝ) := sqrt_pos.2 (by exact_mod_cast hn)
    exact div_neg_of_neg_of_pos (by norm_num) hs
  constructor
  · intro hn
    unfold b
    have hs : 0 < sqrt (n : ℝ) := sqrt_pos.2 (by exact_mod_cast (lt_trans (by norm_num : 0 < 1) hn))
    rw [div_lt_div_iff_of_pos_right hs]
    norm_num
  · intro hn
    unfold b
    have hs : 0 < sqrt (n : ℝ) := sqrt_pos.2 (by exact_mod_cast (lt_trans (by norm_num : 0 < 2008) hn))
    change -log (log (n : ℝ)) / sqrt (n : ℝ) < -2 / sqrt (n : ℝ)

    rw [div_lt_div_iff_of_pos_right hs]
    -- goal? -loglog < -2 or? because > parsed
    suffices (2 : ℝ) < log (log (n : ℝ)) by linarith
    have hnreal : (Real.exp (Real.exp 2) : ℝ) < n := by
      nlinarith [exp_exp_two_lt_2009_aux, show (2009 : ℝ) ≤ n by exact_mod_cast hn]
    have hnpos : (0 : ℝ) < n := by positivity
    have hexp2_lt_logn : Real.exp 2 < log (n : ℝ) := (Real.lt_log_iff_exp_lt hnpos).2 hnreal
    have hlogpos : 0 < log (n : ℝ) := lt_trans (Real.exp_pos 2) hexp2_lt_logn
    exact (Real.lt_log_iff_exp_lt hlogpos).2 hexp2_lt_logn
