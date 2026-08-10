import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real

lemma exp_half_lt_nine_fifths : Real.exp ((1:ℝ)/2) < (9:ℝ)/5 := by
  have h := Real.exp_bound' (x := (1:ℝ)/2) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  norm_num at h ⊢
  linarith

lemma exp_exp_two_lt_2009_test : Real.exp (Real.exp 2) < (2009 : ℝ) := by
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
  exact lt_trans (Real.exp_lt_exp_of_lt hexp2) hexp75
