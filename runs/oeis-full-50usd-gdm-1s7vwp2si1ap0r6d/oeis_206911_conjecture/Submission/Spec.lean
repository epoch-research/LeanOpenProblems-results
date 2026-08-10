import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 500000

open Real Nat Finset Filter

noncomputable def H (n : ℕ) : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

theorem H_zero : H 0 = 0 := by
  rfl

theorem H_succ (n : ℕ) : H (n + 1) = H n + 1 / ((n : ℝ) + 1) := by
  simp [H, sum_range_succ]

noncomputable def A206911 (n : ℕ) : ℕ :=
  -- Define $S_n = \sum_{k=1}^n \frac{1}{k}$
  let S_n_real : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

  -- Count of log terms is $\lfloor e^{S_n} - 1 \rfloor$
  let count_log_terms : ℤ := floor (exp S_n_real - 1)

  -- Final rank: n + count.
  n + count_log_terms.toNat

theorem A206911_eq_H (n : ℕ) : A206911 n = n + (Int.floor (exp (H n) - 1)).toNat := rfl

noncomputable def A206911_diff (n : ℕ) : ℕ := A206911 (n + 1) - A206911 n

theorem H_monotone {m n : ℕ} (h : m ≤ n) : H m ≤ H n := by
  induction' h with d hd id
  · rfl
  · rw [H_succ]
    have : 0 ≤ 1 / ((d : ℝ) + 1) := by positivity
    linarith

theorem H_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ H n := by
  have : H 1 ≤ H n := H_monotone hn
  have h1 : H 1 = 1 := by
    rw [H_succ, H_zero]
    simp
  linarith [h1]

theorem exp_H_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ exp (H n) := by
  have h_zero : 0 ≤ H n := by linarith [H_ge_one n hn]
  have h_exp : exp 0 ≤ exp (H n) := exp_le_exp.mpr h_zero
  rw [exp_zero] at h_exp
  exact h_exp

theorem count_log_terms_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ Int.floor (exp (H n) - 1) := by
  apply Int.floor_nonneg.mpr
  linarith [exp_H_ge_one n hn]

theorem A206911_coe_eq (n : ℕ) (hn : 1 ≤ n) :
  (A206911 n : ℤ) = (n : ℤ) + Int.floor (exp (H n) - 1) := by
  rw [A206911_eq_H]
  simp
  have h_exp_ge : 1 ≤ exp (H n) := exp_H_ge_one n hn
  have h_exp_nonneg : 0 ≤ exp (H n) := by positivity
  have h_floor_ge : 1 ≤ Nat.floor (exp (H n)) := by
    rw [Nat.le_floor_iff h_exp_nonneg]
    exact_mod_cast h_exp_ge
  have h_eq_tonat : (Int.floor (exp (H n))).toNat = Nat.floor (exp (H n)) := by
    rw [← Int.natCast_floor_eq_floor h_exp_nonneg]
    rfl
  rw [h_eq_tonat]
  rw [Nat.cast_sub h_floor_ge]
  rw [Int.natCast_floor_eq_floor h_exp_nonneg]
  rfl

theorem A206911_real_diff_from_coe_diff (n : ℕ)
  (h : (A206911 (n + 1) : ℤ) - (A206911 n : ℤ) = 2 ∨ (A206911 (n + 1) : ℤ) - (A206911 n : ℤ) = 3) :
  A206911 (n + 1) - A206911 n = 2 ∨ A206911 (n + 1) - A206911 n = 3 := by
  omega

theorem coe_diff_eq (n : ℕ) (hn : 1 ≤ n) :
  (A206911 (n + 1) : ℤ) - (A206911 n : ℤ) = 1 + Int.floor (exp (H (n + 1)) - 1) - Int.floor (exp (H n) - 1) := by
  have hn1 : 1 ≤ n + 1 := by omega
  rw [A206911_coe_eq (n + 1) hn1, A206911_coe_eq n hn]
  push_cast
  ring

theorem floor_sub_floor_of_sub_bounds {x y : ℝ} (h1 : 1 < x - y) (h2 : x - y < 2) :
  Int.floor x - Int.floor y = 1 ∨ Int.floor x - Int.floor y = 2 := by
  have h3 : (Int.floor x : ℝ) - (Int.floor y : ℝ) > 0 := by
    -- we know x < Int.floor x + 1
    -- and Int.floor y ≤ y
    have lx : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
    have ly : (Int.floor y : ℝ) ≤ y := Int.floor_le y
    linarith
  have h4 : (Int.floor x : ℝ) - (Int.floor y : ℝ) < 3 := by
    -- Int.floor x ≤ x
    -- y < Int.floor y + 1
    have lx : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have ly : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
    linarith
  have h3' : Int.floor x - Int.floor y ≥ 1 := by
    exact_mod_cast h3
  have h4' : Int.floor x - Int.floor y < 3 := by
    exact_mod_cast h4
  omega

theorem diff_exp_eq (n : ℕ) : exp (H (n + 1)) - exp (H n) = exp (H n) * (exp (1 / ((n : ℝ) + 1)) - 1) := by
  rw [H_succ]
  rw [exp_add]
  ring

theorem exp_H_gt_self_plus_one (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) + 1 < exp (H n) := by
  induction' n, hn using Nat.le_induction with d hd id
  · have h_H1 : H 1 = 1 := by rw [H_succ, H_zero]; simp
    rw [h_H1]
    exact_mod_cast exp_one_gt_two
  · rw [H_succ]
    rw [exp_add]
    have h_exp_frac : 1 / ((d : ℝ) + 1) + 1 < exp (1 / ((d : ℝ) + 1)) := by
      apply add_one_lt_exp
      positivity
    have h_pos : 0 < (d : ℝ) + 1 := by positivity
    have h_pos' : 0 < 1 / ((d : ℝ) + 1) + 1 := by positivity
    have h_prod : ((d : ℝ) + 1) * (1 / ((d : ℝ) + 1) + 1) < exp (H d) * exp (1 / ((d : ℝ) + 1)) := by
      calc ((d : ℝ) + 1) * (1 / ((d : ℝ) + 1) + 1)
        _ < exp (H d) * (1 / ((d : ℝ) + 1) + 1) := mul_lt_mul_of_pos_right id h_pos'
        _ < exp (H d) * exp (1 / ((d : ℝ) + 1)) := mul_lt_mul_of_pos_left h_exp_frac (by positivity)
    have h_lhs : ((d : ℝ) + 1) * (1 / ((d : ℝ) + 1) + 1) = (d : ℝ) + 1 + 1 := by
      have hd_ne : (d : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [h_lhs] at h_prod
    exact_mod_cast h_prod

theorem diff_exp_gt_one (n : ℕ) (hn : 1 ≤ n) : exp (H (n + 1)) - exp (H n) > 1 := by
  rw [diff_exp_eq]
  have h1 : (n : ℝ) + 1 < exp (H n) := exp_H_gt_self_plus_one n hn
  have h2 : 1 / ((n : ℝ) + 1) + 1 < exp (1 / ((n : ℝ) + 1)) := by
    apply add_one_lt_exp
    positivity
  have h3 : 1 / ((n : ℝ) + 1) < exp (1 / ((n : ℝ) + 1)) - 1 := by linarith
  have h_pos : 0 < (n : ℝ) + 1 := by positivity
  have h_pos2 : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have h_prod : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) < exp (H n) * (exp (1 / ((n : ℝ) + 1)) - 1) := by
    calc ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))
      _ < exp (H n) * (1 / ((n : ℝ) + 1)) := mul_lt_mul_of_pos_right h1 h_pos2
      _ < exp (H n) * (exp (1 / ((n : ℝ) + 1)) - 1) := mul_lt_mul_of_pos_left h3 (by positivity)
  have h_cancel : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  linarith

theorem exp_frac_lt (n : ℕ) (hn : 1 ≤ n) : exp (1 / ((n : ℝ) + 1)) < 1 + 1 / (n : ℝ) := by
  have h_pos_frac : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hx : - (1 / ((n : ℝ) + 1)) ≠ 0 := by linarith
  have h_exp : - (1 / ((n : ℝ) + 1)) + 1 < exp (- (1 / ((n : ℝ) + 1))) := add_one_lt_exp hx
  have h_sub : - (1 / ((n : ℝ) + 1)) + 1 = ((n : ℝ) / ((n : ℝ) + 1)) := by
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [h_sub] at h_exp
  have h_exp_pos : 0 < exp (- (1 / ((n : ℝ) + 1))) := by positivity
  have h_frac_pos : 0 < (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have h_recip : 1 / exp (- (1 / ((n : ℝ) + 1))) < 1 / ((n : ℝ) / ((n : ℝ) + 1)) := by
    apply one_div_lt_one_div_of_lt h_frac_pos h_exp
  have h_lhs : 1 / exp (- (1 / ((n : ℝ) + 1))) = exp (1 / ((n : ℝ) + 1)) := by
    rw [one_div, exp_neg, inv_inv]
  have h_rhs : 1 / ((n : ℝ) / ((n : ℝ) + 1)) = 1 + 1 / (n : ℝ) := by
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    have hn1_ne : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [h_lhs, h_rhs] at h_recip
  exact h_recip

theorem exp_H_div_self_decreasing (n : ℕ) (hn : 1 ≤ n) : exp (H (n + 1)) / ((n : ℝ) + 1) < exp (H n) / (n : ℝ) := by
  have h_frac_lt : exp (1 / ((n : ℝ) + 1)) < 1 + 1 / (n : ℝ) := exp_frac_lt n hn
  rw [H_succ, exp_add]
  have h_pos : 0 < (n : ℝ) + 1 := by positivity
  have h_pos2 : 0 < exp (H n) / ((n : ℝ) + 1) := by positivity
  have h1 : exp (H n) * exp (1 / ((n : ℝ) + 1)) / ((n : ℝ) + 1) < exp (H n) * (1 + 1 / (n : ℝ)) / ((n : ℝ) + 1) := by
    have h_mul : exp (H n) * exp (1 / ((n : ℝ) + 1)) < exp (H n) * (1 + 1 / (n : ℝ)) := by
      exact mul_lt_mul_of_pos_left h_frac_lt (by positivity)
    exact div_lt_div_of_pos_right h_mul h_pos
  have h2 : exp (H n) * (1 + 1 / (n : ℝ)) / ((n : ℝ) + 1) = exp (H n) / (n : ℝ) := by
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    have hn1_ne : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  linarith

theorem exp_H_div_self_le_five (n : ℕ) (hn : 5 ≤ n) : exp (H n) / (n : ℝ) ≤ exp (H 5) / 5 := by
  induction' n, hn using Nat.le_induction with d hd id
  · rfl
  · push_cast
    have h_dec : exp (H (d + 1)) / ((d : ℝ) + 1) < exp (H d) / (d : ℝ) := by
      apply exp_H_div_self_decreasing
      omega
    linarith

theorem H_five_value : H 5 = 137 / 60 := by
  repeat rw [H_succ]
  rw [H_zero]
  norm_num

theorem h_near_test : expNear 4 (137 / 180) 0 = 74331413 / 34992000 := by
  unfold expNear
  simp [sum_range_succ, Nat.factorial]
  norm_num

theorem exp_H5_lt_ten : exp (137 / 60) < 10 := by
  have h_bound : |exp (137 / 180) - expNear 4 (137 / 180) 0| ≤ |137 / 180| ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) := by
    apply exp_approx_end 3 4 (137 / 180) (by rfl) (by norm_num)
  have h_near : expNear 4 (137 / 180) 0 = 74331413 / 34992000 := by
    unfold expNear
    simp [sum_range_succ, Nat.factorial]
    norm_num
  have h_exp_lt : exp (137 / 180) < 215 / 100 := by
    rw [h_near] at h_bound
    have h1 : (137 / (180 : ℝ)) ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) < 18 / 1000 := by norm_num
    have h2 : 74331413 / (34992000 : ℝ) < 21251 / 10000 := by norm_num
    have h3 : |(137 / 180 : ℝ)| = 137 / 180 := by norm_num
    rw [h3] at h_bound
    linarith [abs_sub_le_iff.1 h_bound]
  have h_eq : exp (137 / 60) = (exp (137 / 180)) ^ 3 := by
    have : (137 / 60 : ℝ) = 137 / 180 + 137 / 180 + 137 / 180 := by ring
    rw [this]
    repeat rw [exp_add]
    ring
  rw [h_eq]
  have h_ineq : (exp (137 / 180)) ^ 3 < (215 / 100 : ℝ) ^ 3 := by
    have : 0 ≤ exp (137 / 180) := by positivity
    gcongr
  have h_cube : (215 / (100 : ℝ)) ^ 3 < 10 := by norm_num
  exact lt_trans h_ineq h_cube

theorem exp_H5_div_five_lt_two : exp (H 5) / 5 < 2 := by
  rw [H_five_value]
  have : exp (137 / 60) < 10 := exp_H5_lt_ten
  linarith

theorem exp_H_div_self_lt_two (n : ℕ) (hn : 5 ≤ n) : exp (H n) / (n : ℝ) < 2 := by
  have h1 : exp (H n) / (n : ℝ) ≤ exp (H 5) / 5 := exp_H_div_self_le_five n hn
  have h2 : exp (H 5) / 5 < 2 := exp_H5_div_five_lt_two
  linarith

theorem diff_exp_lt_two (n : ℕ) (hn : 5 ≤ n) : exp (H (n + 1)) - exp (H n) < 2 := by
  rw [diff_exp_eq]
  have h_pos : 0 < exp (H n) := by positivity
  have h_frac_lt : exp (1 / ((n : ℝ) + 1)) < 1 + 1 / (n : ℝ) := exp_frac_lt n (by omega)
  have h_frac_sub_lt : exp (1 / ((n : ℝ) + 1)) - 1 < 1 / (n : ℝ) := by linarith
  have h_prod_lt : exp (H n) * (exp (1 / ((n : ℝ) + 1)) - 1) < exp (H n) * (1 / (n : ℝ)) := by
    exact mul_lt_mul_of_pos_left h_frac_sub_lt h_pos
  have h_div : exp (H n) * (1 / (n : ℝ)) = exp (H n) / (n : ℝ) := by ring
  rw [h_div] at h_prod_lt
  have h_five : exp (H n) / (n : ℝ) < 2 := by
    have h_le : exp (H n) / (n : ℝ) ≤ exp (H 5) / 5 := exp_H_div_self_le_five n hn
    have h_lt : exp (H 5) / 5 < 2 := exp_H5_div_five_lt_two
    linarith
  linarith [h_prod_lt]

theorem exp_H2_bounds : 44 / 10 < exp (H 2) ∧ exp (H 2) < 45 / 10 := by
  have h_H2 : H 2 = 3 / 2 := by
    repeat rw [H_succ]
    rw [H_zero]
    norm_num
  have h_bound : |exp (1 / 2) - expNear 4 (1 / 2) 0| ≤ |1 / 2| ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) := by
    apply exp_approx_end 3 4 (1 / 2) (by rfl) (by norm_num)
  have h_near : expNear 4 (1 / 2) 0 = 79 / 48 := by
    unfold expNear
    simp [sum_range_succ, Nat.factorial]
    norm_num
  have h_exp_lower : 2523 / 1536 ≤ exp (1 / 2) := by
    rw [h_near] at h_bound
    have h1 : (1 / (2 : ℝ)) ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) = 5 / 1536 := by norm_num
    have h3 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h3, h1] at h_bound
    linarith [abs_sub_le_iff.1 h_bound]
  have h_exp_upper : exp (1 / 2) ≤ 2533 / 1536 := by
    rw [h_near] at h_bound
    have h1 : (1 / (2 : ℝ)) ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) = 5 / 1536 := by norm_num
    have h3 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h3, h1] at h_bound
    linarith [abs_sub_le_iff.1 h_bound]
  have h_eq : exp (H 2) = (exp (1 / 2)) ^ 3 := by
    rw [h_H2]
    have : (3 / 2 : ℝ) = 1 / 2 + 1 / 2 + 1 / 2 := by ring
    rw [this]
    repeat rw [exp_add]
    ring
  constructor
  · rw [h_eq]
    have : (2523 / 1536 : ℝ) ^ 3 ≤ (exp (1 / 2)) ^ 3 := by
      have : 0 ≤ (2523 / 1536 : ℝ) := by norm_num
      gcongr
    have : (44 / 10 : ℝ) < (2523 / 1536) ^ 3 := by norm_num
    linarith
  · rw [h_eq]
    have : (exp (1 / 2)) ^ 3 ≤ (2533 / 1536 : ℝ) ^ 3 := by
      have : 0 ≤ exp (1 / 2) := by positivity
      gcongr
    have : (2533 / 1536 : ℝ) ^ 3 < 45 / 10 := by norm_num
    linarith

theorem exp_H3_bounds : 611 / 100 < exp (H 3) ∧ exp (H 3) < 63 / 10 := by
  have h_H3 : H 3 = 11 / 6 := by
    repeat rw [H_succ]
    rw [H_zero]
    norm_num
  have h_bound : |exp (11 / 18) - expNear 4 (11 / 18) 0| ≤ |11 / 18| ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) := by
    apply exp_approx_end 3 4 (11 / 18) (by rfl) (by norm_num)
  have h_near : expNear 4 (11 / 18) 0 = 64241 / 34992 := by
    unfold expNear
    simp [sum_range_succ, Nat.factorial]
    norm_num
  have h_exp_lower : 18428203 / 10077696 ≤ exp (11 / 18) := by
    rw [h_near] at h_bound
    have h1 : (11 / (18 : ℝ)) ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) = 73205 / 10077696 := by norm_num
    have h3 : |(11 / 18 : ℝ)| = 11 / 18 := by norm_num
    rw [h3, h1] at h_bound
    linarith [abs_sub_le_iff.1 h_bound]
  have h_exp_upper : exp (11 / 18) ≤ 18574613 / 10077696 := by
    rw [h_near] at h_bound
    have h1 : (11 / (18 : ℝ)) ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) = 73205 / 10077696 := by norm_num
    have h3 : |(11 / 18 : ℝ)| = 11 / 18 := by norm_num
    rw [h3, h1] at h_bound
    linarith [abs_sub_le_iff.1 h_bound]
  have h_eq : exp (H 3) = (exp (11 / 18)) ^ 3 := by
    rw [h_H3]
    have : (11 / 6 : ℝ) = 11 / 18 + 11 / 18 + 11 / 18 := by ring
    rw [this]
    repeat rw [exp_add]
    ring
  constructor
  · rw [h_eq]
    have : (18428203 / 10077696 : ℝ) ^ 3 ≤ (exp (11 / 18)) ^ 3 := by
      have : 0 ≤ (18428203 / 10077696 : ℝ) := by norm_num
      gcongr
    have : (611 / 100 : ℝ) < (18428203 / 10077696) ^ 3 := by norm_num
    linarith
  · rw [h_eq]
    have : (exp (11 / 18)) ^ 3 ≤ (18574613 / 10077696 : ℝ) ^ 3 := by
      have : 0 ≤ exp (11 / 18) := by positivity
      gcongr
    have : (18574613 / 10077696 : ℝ) ^ 3 < 63 / 10 := by norm_num
    linarith


theorem exp_H4_lt_eight_one : exp (H 4) < 805 / 100 := by
  have h_H4 : H 4 = 25 / 12 := by
    repeat rw [H_succ]
    rw [H_zero]
    norm_num
  have h_bound : |exp (25 / 36) - expNear 4 (25 / 36) 0| ≤ |25 / 36| ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) := by
    apply exp_approx_end 3 4 (25 / 36) (by rfl) (by norm_num)
  have h_near : expNear 4 (25 / 36) 0 = 557461 / 279936 := by
    unfold expNear
    simp [sum_range_succ, Nat.factorial]
    norm_num
  have h_exp_upper : exp (25 / 36) ≤ 323050661 / 161243136 := by
    rw [h_near] at h_bound
    have h1 : (25 / (36 : ℝ)) ^ 4 / (Nat.factorial 4 : ℝ) * (((4 : ℝ) + 1) / 4) = 1953125 / 161243136 := by norm_num
    have h3 : |(25 / 36 : ℝ)| = 25 / 36 := by norm_num
    rw [h3, h1] at h_bound
    linarith [abs_sub_le_iff.1 h_bound]
  have h_eq : exp (H 4) = (exp (25 / 36)) ^ 3 := by
    rw [h_H4]
    have : (25 / 12 : ℝ) = 25 / 36 + 25 / 36 + 25 / 36 := by ring
    rw [this]
    repeat rw [exp_add]
    ring
  rw [h_eq]
  have : (exp (25 / 36)) ^ 3 ≤ (323050661 / 161243136 : ℝ) ^ 3 := by
    have : 0 ≤ exp (25 / 36) := by positivity
    gcongr
  have : (323050661 / 161243136 : ℝ) ^ 3 < 805 / 100 := by norm_num
  linarith


theorem exp_H1_bounds : 27 / 10 < exp (H 1) ∧ exp (H 1) < 28 / 10 := by
  have h_H1 : H 1 = 1 := by rw [H_succ, H_zero]; simp
  rw [h_H1]
  constructor
  · linarith [exp_one_gt_d9]
  · linarith [exp_one_lt_d9]



theorem exp_H4_gt_eight : 8 < exp (H 4) := by
  have h_H4 : H 4 = 25 / 12 := by
    repeat rw [H_succ]
    rw [H_zero]
    norm_num
  rw [h_H4]
  have h_eq : (25 / 12 : ℝ) = 1 + 1 + 1 / 12 := by ring
  rw [h_eq]
  repeat rw [exp_add]
  have h_exp_one : 2718281828 / 1000000000 < exp 1 := by
    have : (2.7182818283 : ℝ) < exp 1 := exp_one_gt_d9
    linarith
  have h_exp_frac : 1 / 12 + 1 < exp (1 / 12) := by
    apply add_one_lt_exp
    norm_num
  have h_prod : (2718281828 / 1000000000) ^ 2 * (1 / 12 + 1) < (exp 1) ^ 2 * exp (1 / 12) := by
    have : 0 ≤ (2718281828 / 1000000000 : ℝ) := by norm_num
    have : 0 ≤ exp 1 := by positivity
    gcongr
  have h_calc : (8 : ℝ) < (2718281828 / 1000000000) ^ 2 * (1 / 12 + 1) := by norm_num
  linarith

theorem diff_exp_lt_two_small (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 4) : exp (H (n + 1)) - exp (H n) < 2 := by
  interval_cases n
  · have h1 : exp (H 2) < 45 / 10 := exp_H2_bounds.2
    have h2 : 27 / 10 < exp (H 1) := exp_H1_bounds.1
    linarith
  · have h1 : exp (H 3) < 63 / 10 := exp_H3_bounds.2
    have h2 : 44 / 10 < exp (H 2) := exp_H2_bounds.1
    linarith
  · have h1 : exp (H 4) < 805 / 100 := exp_H4_lt_eight_one
    have h2 : 611 / 100 < exp (H 3) := exp_H3_bounds.1
    linarith
  · have h1 : exp (H 5) < 10 := by
      rw [H_five_value]
      exact exp_H5_lt_ten
    have h2 : 8 < exp (H 4) := exp_H4_gt_eight
    linarith



theorem diff_exp_lt_two_all (n : ℕ) (hn : 1 ≤ n) : exp (H (n + 1)) - exp (H n) < 2 := by
  by_cases h : n ≤ 4
  · exact diff_exp_lt_two_small n hn h
  · have : 5 ≤ n := by omega
    exact diff_exp_lt_two n this

theorem tendsto_const : Tendsto (fun (_ : ℕ) => (355 / 100 : ℝ)) atTop (nhds (355 / 100)) := by
  exact tendsto_const_nhds




theorem oeis_206911_part1_real (n : ℕ) (hn : 1 ≤ n) : A206911 (n + 1) - A206911 n = 2 ∨ A206911 (n + 1) - A206911 n = 3 := by
  have h_diff_eq : (A206911 (n + 1) : ℤ) - (A206911 n : ℤ) = 1 + Int.floor (exp (H (n + 1)) - 1) - Int.floor (exp (H n) - 1) := coe_diff_eq n hn
  have h_bounds_gt : 1 < (exp (H (n + 1)) - 1) - (exp (H n) - 1) := by
    have : exp (H (n + 1)) - exp (H n) > 1 := diff_exp_gt_one n hn
    linarith
  have h_bounds_lt : (exp (H (n + 1)) - 1) - (exp (H n) - 1) < 2 := by
    have : exp (H (n + 1)) - exp (H n) < 2 := diff_exp_lt_two_all n hn
    linarith
  have h_floor_diff := floor_sub_floor_of_sub_bounds h_bounds_gt h_bounds_lt
  have h_coe_diff : (A206911 (n + 1) : ℤ) - (A206911 n : ℤ) = 2 ∨ (A206911 (n + 1) : ℤ) - (A206911 n : ℤ) = 3 := by
    rw [h_diff_eq]
    rcases h_floor_diff with h_one | h_two
    · left
      omega
    · right
      omega
  exact A206911_real_diff_from_coe_diff n h_coe_diff

theorem oeis_206911_part1 (n : ℕ) (hn : 1 ≤ n) : A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  unfold A206911_diff
  exact oeis_206911_part1_real n hn

noncomputable def A206911_count_3s (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

noncomputable def A206911_count_2s (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 2 then 1 else 0


theorem A206911_le (n : ℕ) (hn : 1 ≤ n) : A206911 n ≤ A206911 (n + 1) := by
  have h := oeis_206911_part1_real n hn
  omega

theorem sum_diff_eq_sub (N : ℕ) :
  (∑ n ∈ range N, (A206911_diff (n + 1) : ℤ)) = (A206911 (N + 1) : ℤ) - (A206911 1 : ℤ) := by
  have h : (fun n => (A206911_diff (n + 1) : ℤ)) = (fun n => (A206911 (n + 2) : ℤ) - (A206911 (n + 1) : ℤ)) := by
    ext n
    simp [A206911_diff]
    have hn1 : 1 ≤ n + 1 := by omega
    have h_le : A206911 (n + 1) ≤ A206911 (n + 1 + 1) := A206911_le (n + 1) hn1
    have h_cast : ((A206911 (n + 1 + 1) - A206911 (n + 1) : ℕ) : ℤ) = (A206911 (n + 1 + 1) : ℤ) - (A206911 (n + 1) : ℤ) := Nat.cast_sub h_le
    have h_add : n + 1 + 1 = n + 2 := rfl
    rw [h_add] at h_cast
    rw [h_add]
    exact h_cast
  rw [h]
  exact Finset.sum_range_sub (fun n => (A206911 (n + 1) : ℤ)) N

theorem diff_sub_two_eq_if (n : ℕ) :
  ((A206911_diff (n + 1) : ℤ) - 2) = (if A206911_diff (n + 1) = 3 then 1 else 0 : ℕ) := by
  have h := oeis_206911_part1 (n + 1) (by omega)
  rcases h with h2 | h3
  · rw [h2]; rfl
  · rw [h3]; rfl

theorem count_3s_eq_sum_diff (N : ℕ) :
  (A206911_count_3s N : ℤ) = (∑ n ∈ range N, (A206911_diff (n + 1) : ℤ)) - 2 * N := by
  rw [A206911_count_3s]
  push_cast
  have h_eq : (∑ x ∈ range N, ((A206911_diff (x + 1) : ℤ) - 2)) = ∑ x ∈ range N, (if A206911_diff (x + 1) = 3 then 1 else 0 : ℤ) := by
    apply sum_congr rfl
    intro x _
    have h_cast : ((if A206911_diff (x + 1) = 3 then 1 else 0 : ℕ) : ℤ) = (if A206911_diff (x + 1) = 3 then 1 else 0 : ℤ) := by
      split_ifs <;> rfl
    rw [← h_cast]
    exact diff_sub_two_eq_if x
  rw [← h_eq]
  rw [sum_sub_distrib]
  simp [sum_const]
  ring

theorem A206911_one_eq_two : (A206911 1 : ℤ) = 2 := by
  have : 1 ≤ 1 := by omega
  rw [A206911_coe_eq 1 this]
  have h_bound : 27 / 10 < exp (H 1) ∧ exp (H 1) < 28 / 10 := exp_H1_bounds
  have h_floor : Int.floor (exp (H 1) - 1) = 1 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor
    · linarith [h_bound.1]
    · linarith [h_bound.2]
  rw [h_floor]
  rfl

theorem count_3s_eq_formula (N : ℕ) :
  (A206911_count_3s N : ℤ) = (Int.floor (exp (H (N + 1)) - 1)) - N - 1 := by
  rw [count_3s_eq_sum_diff, sum_diff_eq_sub]
  have hN1 : 1 ≤ N + 1 := by omega
  rw [A206911_coe_eq (N + 1) hN1, A206911_one_eq_two]
  omega




theorem count_sum_eq_id (N : ℕ) : A206911_count_3s N + A206911_count_2s N = N := by
  rw [A206911_count_3s, A206911_count_2s, ← sum_add_distrib]
  have h_eq : (∑ x ∈ range N, ((if A206911_diff (x + 1) = 3 then 1 else 0) + (if A206911_diff (x + 1) = 2 then 1 else 0))) = ∑ x ∈ range N, 1 := by
    apply sum_congr rfl
    intro x _
    have h := oeis_206911_part1 (x + 1) (by omega)
    rcases h with h2 | h3
    · rw [h2]; rfl
    · rw [h3]; rfl
  rw [h_eq]
  simp

theorem count_2s_eq_formula (N : ℕ) :
  (A206911_count_2s N : ℤ) = 2 * N + 1 - (Int.floor (exp (H (N + 1)) - 1)) := by
  have h : (A206911_count_2s N : ℤ) = N - (A206911_count_3s N : ℤ) := by
    have h2 := count_sum_eq_id N
    omega
  rw [h, count_3s_eq_formula]
  omega

theorem H_eq_harmonic (n : ℕ) : H n = (harmonic n : ℝ) := by
  unfold H harmonic
  push_cast
  apply sum_congr rfl
  intro x _
  rw [one_div]

theorem tendsto_H_sub_log :
  Tendsto (fun n : ℕ => H n - Real.log n) atTop (nhds Real.eulerMascheroniConstant) := by
  have h_eq : (fun n : ℕ => H n - Real.log n) = (fun n : ℕ => (harmonic n : ℝ) - Real.log n) := by
    ext n
    rw [H_eq_harmonic]
  rw [h_eq]
  exact Real.tendsto_harmonic_sub_log

theorem tendsto_exp_H_sub_log :
  Tendsto (fun n : ℕ => exp (H n - Real.log n)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
  exact (continuous_exp.tendsto Real.eulerMascheroniConstant).comp tendsto_H_sub_log

theorem exp_sub_log_eq (n : ℕ) (hn : 1 ≤ n) : exp (H n - Real.log n) = exp (H n) / (n : ℝ) := by
  rw [exp_sub]
  have hn_pos : 0 < (n : ℝ) := by positivity
  have h_log : exp (Real.log (n : ℝ)) = (n : ℝ) := exp_log hn_pos
  rw [h_log]

theorem tendsto_exp_H_div_self :
  Tendsto (fun n : ℕ => exp (H n) / (n : ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
  have h_eq : (fun n : ℕ => exp (H n) / (n : ℝ)) =ᶠ[atTop] (fun n : ℕ => exp (H n - Real.log n)) := by
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    exact (exp_sub_log_eq n hn).symm
  exact (tendsto_congr' h_eq).mpr tendsto_exp_H_sub_log

theorem tendsto_one_div_nat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
  have h_eq : (fun n : ℕ => 1 / (n : ℝ)) = (fun n : ℕ => (n : ℝ)⁻¹) := by
    ext n
    rw [one_div]
  rw [h_eq]
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem tendsto_N_add_one_div_N :
  Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) / (N : ℝ))) atTop (nhds 1) := by
  have h_eq : (fun N : ℕ => (((N + 1 : ℕ) : ℝ) / (N : ℝ))) =ᶠ[atTop] (fun N : ℕ => 1 + 1 / (N : ℝ)) := by
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have h_lim : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (nhds (1 + 0)) := by
    apply Tendsto.const_add
    exact tendsto_one_div_nat
  rw [add_zero] at h_lim
  exact (tendsto_congr' h_eq).mpr h_lim

theorem tendsto_exp_H_succ_div_self :
  Tendsto (fun N : ℕ => exp (H (N + 1)) / (N : ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
  have h_eq : (fun N : ℕ => exp (H (N + 1)) / (N : ℝ)) =ᶠ[atTop] fun N : ℕ => (exp (H (N + 1)) / (((N + 1 : ℕ) : ℝ))) * (((N + 1 : ℕ) : ℝ) / (N : ℝ)) := by
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    have hn1_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have h_lim1 : Tendsto (fun N : ℕ => exp (H (N + 1)) / (((N + 1 : ℕ) : ℝ))) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
    have h_lim := tendsto_exp_H_div_self
    exact h_lim.comp (tendsto_add_atTop_nat 1)
  have h_lim2 : Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) / (N : ℝ))) atTop (nhds 1) := tendsto_N_add_one_div_N
  have h_mul := Tendsto.mul h_lim1 h_lim2
  rw [mul_one] at h_mul
  exact (tendsto_congr' h_eq).mpr h_mul

theorem tendsto_floor_div_self :
  Tendsto (fun N : ℕ => (Int.floor (exp (H (N + 1)) - 1) : ℝ) / N) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
  have hf : Tendsto (fun N : ℕ => (exp (H (N + 1)) - 2) / (N : ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
    have h1 : Tendsto (fun N : ℕ => exp (H (N + 1)) / (N : ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := tendsto_exp_H_succ_div_self
    have h2 : Tendsto (fun N : ℕ => 2 / (N : ℝ)) atTop (nhds 0) := by
      have h_lim := tendsto_one_div_nat
      have h_mul := Tendsto.const_mul 2 h_lim
      rw [mul_zero] at h_mul
      have h_eq : (fun N : ℕ => 2 / (N : ℝ)) = (fun N : ℕ => 2 * (1 / (N : ℝ))) := by
        ext N
        ring
      rw [h_eq]
      exact h_mul
    have h_sub := Tendsto.sub h1 h2
    rw [sub_zero] at h_sub
    have h_congr : (fun N : ℕ => (exp (H (N + 1)) - 2) / (N : ℝ)) = (fun N : ℕ => exp (H (N + 1)) / (N : ℝ) - 2 / (N : ℝ)) := by
      ext N
      ring
    rw [h_congr]
    exact h_sub
  have hh : Tendsto (fun N : ℕ => (exp (H (N + 1)) - 1) / (N : ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := by
    have h1 : Tendsto (fun N : ℕ => exp (H (N + 1)) / (N : ℝ)) atTop (nhds (exp Real.eulerMascheroniConstant)) := tendsto_exp_H_succ_div_self
    have h2 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (nhds 0) := tendsto_one_div_nat
    have h_sub := Tendsto.sub h1 h2
    rw [sub_zero] at h_sub
    have h_congr : (fun N : ℕ => (exp (H (N + 1)) - 1) / (N : ℝ)) = (fun N : ℕ => exp (H (N + 1)) / (N : ℝ) - 1 / (N : ℝ)) := by
      ext N
      ring
    rw [h_congr]
    exact h_sub
  have h_le_f : (fun N : ℕ => (exp (H (N + 1)) - 2) / (N : ℝ)) ≤ᶠ[atTop] (fun N : ℕ => (Int.floor (exp (H (N + 1)) - 1) : ℝ) / N) := by
    simp only [EventuallyLE, eventually_atTop]
    use 1
    intro n hn
    have hn_pos : 0 < (n : ℝ) := by positivity
    have h_floor := Int.sub_one_lt_floor (exp (H (n + 1)) - 1)
    have : exp (H (n + 1)) - 2 < Int.floor (exp (H (n + 1)) - 1) := by linarith
    exact (div_lt_div_of_pos_right this hn_pos).le
  have h_le_h : (fun N : ℕ => (Int.floor (exp (H (N + 1)) - 1) : ℝ) / N) ≤ᶠ[atTop] (fun N : ℕ => (exp (H (N + 1)) - 1) / (N : ℝ)) := by
    simp only [EventuallyLE, eventually_atTop]
    use 1
    intro n hn
    have hn_pos : 0 < (n : ℝ) := by positivity
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have h_floor := Int.floor_le (exp (H (n + 1)) - 1)
    exact div_le_div_of_nonneg_right h_floor hn_nonneg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hh h_le_f h_le_h


theorem test_harm1 : (harmonic 512 : ℝ) > 68165 / 10000 := by
  unfold harmonic
  norm_num

theorem test_harm2 : (harmonic 1024 : ℝ) < 75092 / 10000 := by
  unfold harmonic
  norm_num


theorem log_513_bound : Real.log 513 ≤ 9 * Real.log 2 + 1 / 512 := by
  have h_log_mul : Real.log 513 = Real.log 512 + Real.log (513 / 512) := by
    have h_eq : (513 : ℝ) = 512 * (513 / 512) := by norm_num
    have h_log_eq : Real.log 513 = Real.log (512 * (513 / 512)) := congr_arg Real.log h_eq
    rw [h_log_eq, Real.log_mul (by norm_num) (by norm_num)]
  have h_log_frac : Real.log (513 / 512) ≤ 1 / 512 := by
    have h_le := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 513 / 512)
    linarith
  have h_log_512 : Real.log 512 = 9 * Real.log 2 := by
    have h_eq : (512 : ℝ) = 2 ^ 9 := by norm_num
    rw [h_eq, Real.log_pow]
    push_cast
    rfl
  linarith

theorem eulerMascheroniConstant_gt_576 : 576 / 1000 < Real.eulerMascheroniConstant := by
  have h_seq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 512
  have h_seq_def : Real.eulerMascheroniSeq 512 = (harmonic 512 : ℝ) - Real.log 513 := by
    unfold Real.eulerMascheroniSeq
    norm_num
  have h1 : (harmonic 512 : ℝ) > 68165 / 10000 := test_harm1
  have h2 : Real.log 513 ≤ 9 * Real.log 2 + 1 / 512 := log_513_bound
  have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h_seq_gt : 576 / 1000 < (harmonic 512 : ℝ) - Real.log 513 := by
    linarith
  rw [h_seq_def] at h_seq
  linarith

theorem eulerMascheroniConstant_lt_578 : Real.eulerMascheroniConstant < 578 / 1000 := by
  have h_seq := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  have h_seq_def : Real.eulerMascheroniSeq' 1024 = (harmonic 1024 : ℝ) - Real.log 1024 := rfl
  have h1 : (harmonic 1024 : ℝ) < 75092 / 10000 := test_harm2
  have h_log_1024 : Real.log 1024 = 10 * Real.log 2 := by
    have h_eq : (1024 : ℝ) = 2 ^ 10 := by norm_num
    rw [h_eq, Real.log_pow]
    push_cast
    rfl
  have h3 : Real.log 2 > 0.6931471803 := Real.log_two_gt_d9
  have h_seq_lt : (harmonic 1024 : ℝ) - Real.log 1024 < 578 / 1000 := by
    linarith
  rw [h_seq_def] at h_seq
  linarith


theorem exp_576_bound : 16 / 9 < exp (576 / 1000) := by
  have h_bound : |exp (576 / 1000) - expNear 6 (576 / 1000) 0| ≤ |576 / 1000| ^ 6 / (Nat.factorial 6 : ℝ) * ((((6 : ℕ) : ℝ) + 1) / ((6 : ℕ) : ℝ)) := by
    apply exp_approx_end 5 6 (576 / 1000) (by rfl) (by norm_num)
  have h_near : expNear 6 (576 / 1000) 0 = 271431477193 / 152587890625 := by
    unfold expNear
    simp [sum_range_succ, Nat.factorial]
    norm_num
  have h_abs : |(576 / 1000 : ℝ)| = 576 / 1000 := by norm_num
  have h_six : ((((6 : ℕ) : ℝ) + 1) / ((6 : ℕ) : ℝ)) = 7 / 6 := by norm_num
  rw [h_near, h_abs, h_six] at h_bound
  have h_fact : (Nat.factorial 6 : ℝ) = 720 := by rfl
  rw [h_fact] at h_bound
  have h_bound' : exp (576 / 1000) ≥ 271431477193 / 152587890625 - (576 / 1000) ^ 6 / 720 * (7 / 6) := by
    have h_and := abs_sub_le_iff.1 h_bound
    linarith [h_and.2]
  have h_gt : 16 / 9 < (271431477193 : ℝ) / 152587890625 - (576 / 1000) ^ 6 / 720 * (7 / 6) := by norm_num
  exact lt_of_lt_of_le h_gt h_bound'

theorem exp_578_bound : exp (578 / 1000) < 41 / 23 := by
  have h_bound : |exp (578 / 1000) - expNear 6 (578 / 1000) 0| ≤ |578 / 1000| ^ 6 / (Nat.factorial 6 : ℝ) * ((((6 : ℕ) : ℝ) + 1) / ((6 : ℕ) : ℝ)) := by
    apply exp_approx_end 5 6 (578 / 1000) (by rfl) (by norm_num)
  have h_near : expNear 6 (578 / 1000) 0 = (6684050732502949 : ℝ) / 3750000000000000 := by
    unfold expNear
    simp [sum_range_succ, Nat.factorial]
    norm_num
  have h_abs : |(578 / 1000 : ℝ)| = 578 / 1000 := by norm_num
  have h_six : ((((6 : ℕ) : ℝ) + 1) / ((6 : ℕ) : ℝ)) = 7 / 6 := by norm_num
  rw [h_near, h_abs, h_six] at h_bound
  have h_fact : (Nat.factorial 6 : ℝ) = 720 := by rfl
  rw [h_fact] at h_bound
  have h_bound' : exp (578 / 1000) ≤ (6684050732502949 : ℝ) / 3750000000000000 + (578 / 1000) ^ 6 / 720 * (7 / 6) := by
    have h_and := abs_sub_le_iff.1 h_bound
    linarith [h_and.1]
  have h_lt : (6684050732502949 : ℝ) / 3750000000000000 + (578 / 1000) ^ 6 / 720 * (7 / 6) < 41 / 23 := by norm_num
  exact lt_of_le_of_lt h_bound' h_lt

theorem exp_eulerMascheroniConstant_bounds : 16 / 9 < exp Real.eulerMascheroniConstant ∧ exp Real.eulerMascheroniConstant < 41 / 23 := by
  have h_gt := eulerMascheroniConstant_gt_576
  have h_lt := eulerMascheroniConstant_lt_578
  have h_exp_gt : exp (576 / 1000) < exp Real.eulerMascheroniConstant := exp_lt_exp.mpr h_gt
  have h_exp_lt : exp Real.eulerMascheroniConstant < exp (578 / 1000) := exp_lt_exp.mpr h_lt
  have h1 : 16 / 9 < exp (576 / 1000) := exp_576_bound
  have h2 : exp (578 / 1000) < 41 / 23 := exp_578_bound
  constructor
  · exact lt_trans h1 h_exp_gt
  · exact lt_trans h_exp_lt h2





theorem count_3s_coe_eq (N : ℕ) :
  (A206911_count_3s N : ℝ) = (Int.floor (exp (H (N + 1)) - 1) : ℝ) - N - 1 := by
  have h := count_3s_eq_formula N
  exact_mod_cast h

theorem count_2s_coe_eq (N : ℕ) :
  (A206911_count_2s N : ℝ) = 2 * (N : ℝ) + 1 - (Int.floor (exp (H (N + 1)) - 1) : ℝ) := by
  have h := count_2s_eq_formula N
  exact_mod_cast h

theorem tendsto_count_3s_div_id :
  Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / N) atTop (nhds (exp Real.eulerMascheroniConstant - 1)) := by
  have h_eq : (fun N : ℕ => (A206911_count_3s N : ℝ) / N) =ᶠ[atTop] fun N : ℕ => ((Int.floor (exp (H (N + 1)) - 1) : ℝ) / N) - 1 - 1 / N := by
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    rw [count_3s_coe_eq]
    field_simp
  have h1 : Tendsto (fun N : ℕ => ((Int.floor (exp (H (N + 1)) - 1) : ℝ) / N)) atTop (nhds (exp Real.eulerMascheroniConstant)) := tendsto_floor_div_self
  have h2 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h3 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := tendsto_one_div_nat
  have h_sub := Tendsto.sub h1 h2
  have h_sub2 := Tendsto.sub h_sub h3
  rw [sub_zero] at h_sub2
  exact (tendsto_congr' h_eq).mpr h_sub2

theorem tendsto_count_2s_div_id :
  Tendsto (fun N : ℕ => (A206911_count_2s N : ℝ) / N) atTop (nhds (2 - exp Real.eulerMascheroniConstant)) := by
  have h_eq : (fun N : ℕ => (A206911_count_2s N : ℝ) / N) =ᶠ[atTop] fun N : ℕ => 2 + 1 / N - ((Int.floor (exp (H (N + 1)) - 1) : ℝ) / N) := by
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    rw [count_2s_coe_eq]
    field_simp
  have h1 : Tendsto (fun N : ℕ => ((Int.floor (exp (H (N + 1)) - 1) : ℝ) / N)) atTop (nhds (exp Real.eulerMascheroniConstant)) := tendsto_floor_div_self
  have h2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have h3 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := tendsto_one_div_nat
  have h_add := Tendsto.add h2 h3
  have h_sub := Tendsto.sub h_add h1
  rw [add_zero] at h_sub
  exact (tendsto_congr' h_eq).mpr h_sub



theorem div_div_div_cancel_n (a b : ℝ) {n : ℝ} (hn : n ≠ 0) :
  (a / n) / (b / n) = a / b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [zero_div, div_zero]
  · field_simp

theorem tendsto_ratio :
  Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds ((exp Real.eulerMascheroniConstant - 1) / (2 - exp Real.eulerMascheroniConstant))) := by
  have h1 : Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / N) atTop (nhds (exp Real.eulerMascheroniConstant - 1)) := tendsto_count_3s_div_id
  have h2 : Tendsto (fun N : ℕ => (A206911_count_2s N : ℝ) / N) atTop (nhds (2 - exp Real.eulerMascheroniConstant)) := tendsto_count_2s_div_id
  have h_ne : 2 - exp Real.eulerMascheroniConstant ≠ 0 := by
    have h_bound := exp_eulerMascheroniConstant_bounds
    linarith [h_bound.2]
  have h_div := Tendsto.div h1 h2 h_ne
  have h_eq : (fun N : ℕ => ((A206911_count_3s N : ℝ) / N) / ((A206911_count_2s N : ℝ) / N)) =ᶠ[atTop] (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) := by
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    have h_n_pos : (n : ℝ) ≠ 0 := by positivity
    exact div_div_div_cancel_n (A206911_count_3s n : ℝ) (A206911_count_2s n : ℝ) h_n_pos
  exact (tendsto_congr' h_eq).mp h_div

theorem oeis_206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) ∧
  (∃ L : ℝ,
     (35/10 : ℝ) < L ∧ L < (36/10 : ℝ) ∧
     Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds L)) := by
  constructor
  · exact oeis_206911_part1
  · use (exp Real.eulerMascheroniConstant - 1) / (2 - exp Real.eulerMascheroniConstant)
    have h_bounds := exp_eulerMascheroniConstant_bounds
    have h_limit : (35/10 : ℝ) < (exp Real.eulerMascheroniConstant - 1) / (2 - exp Real.eulerMascheroniConstant) ∧
                   (exp Real.eulerMascheroniConstant - 1) / (2 - exp Real.eulerMascheroniConstant) < (36/10 : ℝ) := by
      have h_pos : 2 - exp Real.eulerMascheroniConstant > 0 := by
        linarith [h_bounds.2]
      constructor
      · rw [lt_div_iff₀ h_pos]
        linarith [h_bounds.1]
      · rw [div_lt_iff₀ h_pos]
        linarith [h_bounds.2]
    refine ⟨h_limit.1, h_limit.2, tendsto_ratio⟩

















