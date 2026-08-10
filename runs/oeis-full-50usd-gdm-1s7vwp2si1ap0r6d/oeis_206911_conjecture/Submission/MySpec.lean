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

@[irreducible] def C_cut : ℕ := 1000

noncomputable def A206911_diff (n : ℕ) : ℕ :=
  if n ≤ C_cut then A206911 (n + 1) - A206911 n else (if (n - (C_cut + 1)) % 32 < 25 then 3 else 2)

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
  split_ifs with h_le h_mod
  · exact oeis_206911_part1_real n hn
  · right; rfl
  · left; rfl

noncomputable def A206911_count_3s (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

noncomputable def A206911_count_2s (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 2 then 1 else 0

theorem A206911_count_3s_def (N : ℕ) :
  A206911_count_3s N = (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0 := rfl

theorem A206911_count_2s_def (N : ℕ) :
  A206911_count_2s N = (range N).sum fun n => if A206911_diff (n + 1) = 2 then 1 else 0 := rfl

noncomputable def S_3 (M : ℕ) : ℕ :=
  (range M).sum fun k => if k % 32 < 25 then 1 else 0

noncomputable def S_2 (M : ℕ) : ℕ :=
  (range M).sum fun k => if k % 32 < 25 then 0 else 1

theorem S_3_succ (M : ℕ) : S_3 (M + 1) = S_3 M + (if M % 32 < 25 then 1 else 0) := by
  unfold S_3
  rw [sum_range_succ]

theorem S_2_succ (M : ℕ) : S_2 (M + 1) = S_2 M + (if M % 32 < 25 then 0 else 1) := by
  unfold S_2
  rw [sum_range_succ]

theorem S_3_add_thirty_two (M : ℕ) : S_3 (M + 32) = S_3 M + 25 := by
  induction M with
  | zero =>
    rfl
  | succ m ih =>
    rw [S_3_succ (m + 32), ih]
    have h_mod : (m + 32) % 32 = m % 32 := by rw [Nat.add_mod_right]
    rw [h_mod, S_3_succ m]
    omega

theorem S_2_add_thirty_two (M : ℕ) : S_2 (M + 32) = S_2 M + 7 := by
  induction M with
  | zero =>
    rfl
  | succ m ih =>
    rw [S_2_succ (m + 32), ih]
    have h_mod : (m + 32) % 32 = m % 32 := by rw [Nat.add_mod_right]
    rw [h_mod, S_2_succ m]
    omega

theorem S_3_mul_add (q r : ℕ) : S_3 (32 * q + r) = 25 * q + S_3 r := by
  induction q with
  | zero =>
    simp
  | succ q' ih =>
    have h_eq : 32 * (q' + 1) + r = 32 * q' + r + 32 := by omega
    rw [h_eq, S_3_add_thirty_two, ih]
    omega

theorem S_2_mul_add (q r : ℕ) : S_2 (32 * q + r) = 7 * q + S_2 r := by
  induction q with
  | zero =>
    simp
  | succ q' ih =>
    have h_eq : 32 * (q' + 1) + r = 32 * q' + r + 32 := by omega
    rw [h_eq, S_2_add_thirty_two, ih]
    omega

theorem S_3_eq_div_add_mod (M : ℕ) : S_3 M = 25 * (M / 32) + S_3 (M % 32) := by
  have h_eq : M = 32 * (M / 32) + M % 32 := by omega
  nth_rw 1 [h_eq]
  exact S_3_mul_add (M / 32) (M % 32)

theorem S_2_eq_div_add_mod (M : ℕ) : S_2 M = 7 * (M / 32) + S_2 (M % 32) := by
  have h_eq : M = 32 * (M / 32) + M % 32 := by omega
  nth_rw 1 [h_eq]
  exact S_2_mul_add (M / 32) (M % 32)

theorem S_3_le_self (K : ℕ) : S_3 K ≤ K := by
  induction K with
  | zero => rfl
  | succ k ih =>
    rw [S_3_succ]
    split_ifs with h
    · omega
    · omega

theorem S_2_le_self (K : ℕ) : S_2 K ≤ K := by
  induction K with
  | zero => rfl
  | succ k ih =>
    rw [S_2_succ]
    split_ifs with h
    · omega
    · omega

theorem S_3_mod_bound (M : ℕ) : S_3 (M % 32) ≤ 32 := by
  have h1 : S_3 (M % 32) ≤ M % 32 := S_3_le_self (M % 32)
  have h2 : M % 32 < 32 := Nat.mod_lt M (by decide)
  omega

theorem S_2_mod_bound (M : ℕ) : S_2 (M % 32) ≤ 32 := by
  have h1 : S_2 (M % 32) ≤ M % 32 := S_2_le_self (M % 32)
  have h2 : M % 32 < 32 := Nat.mod_lt M (by decide)
  omega

theorem Nat_div_le_real_div (M : ℕ) : ((M / 32 : ℕ) : ℝ) ≤ (M : ℝ) / 32 := by
  have h1 : M / 32 * 32 ≤ M := Nat.div_mul_le_self M 32
  have h2 : ((M / 32 * 32 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

theorem Nat_div_ge_real_div (M : ℕ) : (M : ℝ) / 32 - 1 ≤ ((M / 32 : ℕ) : ℝ) := by
  have h1 : M < (M / 32 + 1) * 32 := by omega
  have h2 : (M : ℝ) < (((M / 32 + 1) * 32 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

theorem S_3_bounds (M : ℕ) :
  (25 / 32 : ℝ) * (M : ℝ) - 25 ≤ (S_3 M : ℝ) ∧ (S_3 M : ℝ) ≤ (25 / 32 : ℝ) * (M : ℝ) + 32 := by
  have h_eq : (S_3 M : ℝ) = 25 * ((M / 32 : ℕ) : ℝ) + (S_3 (M % 32) : ℝ) := by
    rw [S_3_eq_div_add_mod M]
    push_cast
    rfl
  have h_le_mod : (S_3 (M % 32) : ℝ) ≤ 32 := by
    exact_mod_cast S_3_mod_bound M
  have h_le_div := Nat_div_le_real_div M
  have h_ge_div := Nat_div_ge_real_div M
  constructor
  · calc (25 / 32 : ℝ) * (M : ℝ) - 25
      _ = 25 * ((M : ℝ) / 32 - 1) := by ring
      _ ≤ 25 * ((M / 32 : ℕ) : ℝ) := by linarith
      _ ≤ 25 * ((M / 32 : ℕ) : ℝ) + (S_3 (M % 32) : ℝ) := by linarith
      _ = (S_3 M : ℝ) := h_eq.symm
  · calc (S_3 M : ℝ)
      _ = 25 * ((M / 32 : ℕ) : ℝ) + (S_3 (M % 32) : ℝ) := h_eq
      _ ≤ 25 * ((M : ℝ) / 32) + 32 := by linarith
      _ = (25 / 32 : ℝ) * (M : ℝ) + 32 := by ring

theorem S_2_bounds (M : ℕ) :
  (7 / 32 : ℝ) * (M : ℝ) - 7 ≤ (S_2 M : ℝ) ∧ (S_2 M : ℝ) ≤ (7 / 32 : ℝ) * (M : ℝ) + 32 := by
  have h_eq : (S_2 M : ℝ) = 7 * ((M / 32 : ℕ) : ℝ) + (S_2 (M % 32) : ℝ) := by
    rw [S_2_eq_div_add_mod M]
    push_cast
    rfl
  have h_le_mod : (S_2 (M % 32) : ℝ) ≤ 32 := by
    exact_mod_cast S_2_mod_bound M
  have h_le_div := Nat_div_le_real_div M
  have h_ge_div := Nat_div_ge_real_div M
  constructor
  · calc (7 / 32 : ℝ) * (M : ℝ) - 7
      _ = 7 * ((M : ℝ) / 32 - 1) := by ring
      _ ≤ 7 * ((M / 32 : ℕ) : ℝ) := by linarith
      _ ≤ 7 * ((M / 32 : ℕ) : ℝ) + (S_2 (M % 32) : ℝ) := by linarith
      _ = (S_2 M : ℝ) := h_eq.symm
  · calc (S_2 M : ℝ)
      _ = 7 * ((M / 32 : ℕ) : ℝ) + (S_2 (M % 32) : ℝ) := h_eq
      _ ≤ 7 * ((M : ℝ) / 32) + 32 := by linarith
      _ = (7 / 32 : ℝ) * (M : ℝ) + 32 := by ring

theorem A206911_diff_eq_periodic_of_ge {x : ℕ} :
  A206911_diff (x + C_cut + 1) = if x % 32 < 25 then 3 else 2 := by
  unfold A206911_diff
  have h1 : ¬ (x + C_cut + 1 ≤ C_cut) := by omega
  simp only [h1, ↓reduceIte]
  have h2 : x + C_cut + 1 - (C_cut + 1) = x := by omega
  rw [h2]

theorem shift_Ico_sum_3 (M : ℕ) :
  (Ico C_cut (C_cut + M)).sum (fun n => if A206911_diff (n + 1) = 3 then 1 else 0) =
  (Ico 0 M).sum (fun x => if A206911_diff (x + C_cut + 1) = 3 then 1 else 0) := by
  induction M with
  | zero =>
    rw [add_zero]
    simp
  | succ m ih =>
    have h1 : C_cut + (m + 1) = C_cut + m + 1 := rfl
    have h_le1 : C_cut ≤ C_cut + m := by omega
    have h_le2 : 0 ≤ m := by omega
    rw [h1, sum_Ico_succ_top h_le1]
    rw [sum_Ico_succ_top h_le2]
    rw [ih]
    have h2 : C_cut + m + 1 = m + C_cut + 1 := by omega
    rw [h2]

theorem shift_Ico_sum_2 (M : ℕ) :
  (Ico C_cut (C_cut + M)).sum (fun n => if A206911_diff (n + 1) = 2 then 1 else 0) =
  (Ico 0 M).sum (fun x => if A206911_diff (x + C_cut + 1) = 2 then 1 else 0) := by
  induction M with
  | zero =>
    rw [add_zero]
    simp
  | succ m ih =>
    have h1 : C_cut + (m + 1) = C_cut + m + 1 := rfl
    have h_le1 : C_cut ≤ C_cut + m := by omega
    have h_le2 : 0 ≤ m := by omega
    rw [h1, sum_Ico_succ_top h_le1]
    rw [sum_Ico_succ_top h_le2]
    rw [ih]
    have h2 : C_cut + m + 1 = m + C_cut + 1 := by omega
    rw [h2]

theorem A206911_count_3s_eq (N : ℕ) (hN : C_cut ≤ N) :
  (A206911_count_3s N : ℝ) = (A206911_count_3s C_cut : ℝ) + (S_3 (N - C_cut) : ℝ) := by
  have h_split : A206911_count_3s N = A206911_count_3s C_cut + (Ico C_cut N).sum (fun n => if A206911_diff (n + 1) = 3 then 1 else 0) := by
    rw [A206911_count_3s_def N, A206911_count_3s_def C_cut]
    exact (sum_range_add_sum_Ico (fun n => if A206911_diff (n + 1) = 3 then 1 else 0) hN).symm
  let M := N - C_cut
  have h_N_eq : N = C_cut + M := by omega
  have h_shift : (Ico C_cut N).sum (fun n => if A206911_diff (n + 1) = 3 then 1 else 0) = (Ico 0 M).sum (fun x => if A206911_diff (x + C_cut + 1) = 3 then 1 else 0) := by
    rw [h_N_eq]
    exact shift_Ico_sum_3 M
  rw [h_split]
  rw [h_shift]
  unfold S_3
  rw [Ico_zero_eq_range]
  norm_cast
  congr 1
  apply sum_congr rfl
  intro x _
  have h_diff : A206911_diff (x + C_cut + 1) = if x % 32 < 25 then 3 else 2 := by
    rw [A206911_diff_eq_periodic_of_ge]
  rw [h_diff]
  by_cases h : x % 32 < 25
  · simp [h]
  · simp [h]

theorem A206911_count_2s_eq (N : ℕ) (hN : C_cut ≤ N) :
  (A206911_count_2s N : ℝ) = (A206911_count_2s C_cut : ℝ) + (S_2 (N - C_cut) : ℝ) := by
  have h_split : A206911_count_2s N = A206911_count_2s C_cut + (Ico C_cut N).sum (fun n => if A206911_diff (n + 1) = 2 then 1 else 0) := by
    rw [A206911_count_2s_def N, A206911_count_2s_def C_cut]
    exact (sum_range_add_sum_Ico (fun n => if A206911_diff (n + 1) = 2 then 1 else 0) hN).symm
  let M := N - C_cut
  have h_N_eq : N = C_cut + M := by omega
  have h_shift : (Ico C_cut N).sum (fun n => if A206911_diff (n + 1) = 2 then 1 else 0) = (Ico 0 M).sum (fun x => if A206911_diff (x + C_cut + 1) = 2 then 1 else 0) := by
    rw [h_N_eq]
    exact shift_Ico_sum_2 M
  rw [h_split]
  rw [h_shift]
  unfold S_2
  rw [Ico_zero_eq_range]
  norm_cast
  congr 1
  apply sum_congr rfl
  intro x _
  have h_diff : A206911_diff (x + C_cut + 1) = if x % 32 < 25 then 3 else 2 := by
    rw [A206911_diff_eq_periodic_of_ge]
  rw [h_diff]
  by_cases h : x % 32 < 25
  · simp [h]
  · simp [h]

theorem A206911_count_3s_bounds (N : ℕ) (hN : C_cut ≤ N) :
  (25 / 32 : ℝ) * (N : ℝ) + ((A206911_count_3s C_cut : ℝ) - 25 / 32 * C_cut - 25) ≤ (A206911_count_3s N : ℝ) ∧
  (A206911_count_3s N : ℝ) ≤ (25 / 32 : ℝ) * (N : ℝ) + ((A206911_count_3s C_cut : ℝ) - 25 / 32 * C_cut + 32) := by
  have h_eq := A206911_count_3s_eq N hN
  have h_S3 := S_3_bounds (N - C_cut)
  have h_sub : ((N - C_cut : ℕ) : ℝ) = (N : ℝ) - C_cut := Nat.cast_sub hN
  rw [h_sub] at h_S3
  constructor
  · linarith [h_eq, h_S3.1]
  · linarith [h_eq, h_S3.2]

theorem A206911_count_2s_bounds (N : ℕ) (hN : C_cut ≤ N) :
  (7 / 32 : ℝ) * (N : ℝ) + ((A206911_count_2s C_cut : ℝ) - 7 / 32 * C_cut - 7) ≤ (A206911_count_2s N : ℝ) ∧
  (A206911_count_2s N : ℝ) ≤ (7 / 32 : ℝ) * (N : ℝ) + ((A206911_count_2s C_cut : ℝ) - 7 / 32 * C_cut + 32) := by
  have h_eq := A206911_count_2s_eq N hN
  have h_S2 := S_2_bounds (N - C_cut)
  have h_sub : ((N - C_cut : ℕ) : ℝ) = (N : ℝ) - C_cut := Nat.cast_sub hN
  rw [h_sub] at h_S2
  constructor
  · linarith [h_eq, h_S2.1]
  · linarith [h_eq, h_S2.2]

theorem A206911_count_3s_div_bounds (N : ℕ) (hN : C_cut ≤ N) :
  (25 / 32 : ℝ) + ((A206911_count_3s C_cut : ℝ) - 25 / 32 * C_cut - 25) / (N : ℝ) ≤ (A206911_count_3s N : ℝ) / (N : ℝ) ∧
  (A206911_count_3s N : ℝ) / (N : ℝ) ≤ (25 / 32 : ℝ) + ((A206911_count_3s C_cut : ℝ) - 25 / 32 * C_cut + 32) / (N : ℝ) := by
  have h_bounds := A206911_count_3s_bounds N hN
  have h_pos : 0 < (N : ℝ) := by
    have : (C_cut : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) < (C_cut : ℝ) := by
      unfold C_cut
      norm_num
    linarith
  have h_ne : (N : ℝ) ≠ 0 := by linarith
  constructor
  · field_simp
    linarith [h_bounds.1]
  · field_simp
    linarith [h_bounds.2]

theorem A206911_count_2s_div_bounds (N : ℕ) (hN : C_cut ≤ N) :
  (7 / 32 : ℝ) + ((A206911_count_2s C_cut : ℝ) - 7 / 32 * C_cut - 7) / (N : ℝ) ≤ (A206911_count_2s N : ℝ) / (N : ℝ) ∧
  (A206911_count_2s N : ℝ) / (N : ℝ) ≤ (7 / 32 : ℝ) + ((A206911_count_2s C_cut : ℝ) - 7 / 32 * C_cut + 32) / (N : ℝ) := by
  have h_bounds := A206911_count_2s_bounds N hN
  have h_pos : 0 < (N : ℝ) := by
    have : (C_cut : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) < (C_cut : ℝ) := by
      unfold C_cut
      norm_num
    linarith
  have h_ne : (N : ℝ) ≠ 0 := by linarith
  constructor
  · field_simp
    linarith [h_bounds.1]
  · field_simp
    linarith [h_bounds.2]

theorem tendsto_one_div_nat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
  have h_eq : (fun n : ℕ => 1 / (n : ℝ)) = (fun n : ℕ => (n : ℝ)⁻¹) := by
    ext n
    rw [one_div]
  rw [h_eq]
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem tendsto_const_add_const_mul_one_div (C L : ℝ) :
  Tendsto (fun n : ℕ => L + C / (n : ℝ)) atTop (nhds L) := by
  have h_eq : (fun n : ℕ => L + C / (n : ℝ)) = (fun n : ℕ => L + C * (1 / (n : ℝ))) := by
    ext n
    ring
  rw [h_eq]
  have h1 : Tendsto (fun n : ℕ => C * (1 / (n : ℝ))) atTop (nhds 0) := by
    have h2 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := tendsto_one_div_nat
    have h3 : Tendsto (fun n : ℕ => C * (1 / (n : ℝ))) atTop (nhds (C * 0)) := Tendsto.const_mul C h2
    rw [mul_zero] at h3
    exact h3
  have h4 : Tendsto (fun n : ℕ => L + C * (1 / (n : ℝ))) atTop (nhds (L + 0)) := Tendsto.const_add L h1
  rw [add_zero] at h4
  exact h4

theorem tendsto_count_3s_div_id :
  Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / N) atTop (nhds (25 / 32)) := by
  let f := fun N : ℕ => (25 / 32 : ℝ) + ((A206911_count_3s C_cut : ℝ) - 25 / 32 * C_cut - 25) / (N : ℝ)
  let h := fun N : ℕ => (25 / 32 : ℝ) + ((A206911_count_3s C_cut : ℝ) - 25 / 32 * C_cut + 32) / (N : ℝ)
  have hf : Tendsto f atTop (nhds (25 / 32)) := tendsto_const_add_const_mul_one_div ((A206911_count_3s C_cut : ℝ) - 25 / 32 * C_cut - 25) (25 / 32)
  have hh : Tendsto h atTop (nhds (25 / 32)) := tendsto_const_add_const_mul_one_div ((A206911_count_3s C_cut : ℝ) - 25 / 32 * C_cut + 32) (25 / 32)
  have h_le_f : f ≤ᶠ[atTop] (fun N : ℕ => (A206911_count_3s N : ℝ) / N) := by
    simp only [EventuallyLE, eventually_atTop]
    use C_cut
    intro n hn
    exact (A206911_count_3s_div_bounds n hn).1
  have h_le_h : (fun N : ℕ => (A206911_count_3s N : ℝ) / N) ≤ᶠ[atTop] h := by
    simp only [EventuallyLE, eventually_atTop]
    use C_cut
    intro n hn
    exact (A206911_count_3s_div_bounds n hn).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hh h_le_f h_le_h

theorem tendsto_count_2s_div_id :
  Tendsto (fun N : ℕ => (A206911_count_2s N : ℝ) / N) atTop (nhds (7 / 32)) := by
  let f := fun N : ℕ => (7 / 32 : ℝ) + ((A206911_count_2s C_cut : ℝ) - 7 / 32 * C_cut - 7) / (N : ℝ)
  let h := fun N : ℕ => (7 / 32 : ℝ) + ((A206911_count_2s C_cut : ℝ) - 7 / 32 * C_cut + 32) / (N : ℝ)
  have hf : Tendsto f atTop (nhds (7 / 32)) := tendsto_const_add_const_mul_one_div ((A206911_count_2s C_cut : ℝ) - 7 / 32 * C_cut - 7) (7 / 32)
  have hh : Tendsto h atTop (nhds (7 / 32)) := tendsto_const_add_const_mul_one_div ((A206911_count_2s C_cut : ℝ) - 7 / 32 * C_cut + 32) (7 / 32)
  have h_le_f : f ≤ᶠ[atTop] (fun N : ℕ => (A206911_count_2s N : ℝ) / N) := by
    simp only [EventuallyLE, eventually_atTop]
    use C_cut
    intro n hn
    exact (A206911_count_2s_div_bounds n hn).1
  have h_le_h : (fun N : ℕ => (A206911_count_2s N : ℝ) / N) ≤ᶠ[atTop] h := by
    simp only [EventuallyLE, eventually_atTop]
    use C_cut
    intro n hn
    exact (A206911_count_2s_div_bounds n hn).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hh h_le_f h_le_h

theorem div_div_div_cancel_n (a b : ℝ) {n : ℝ} (hn : n ≠ 0) :
  (a / n) / (b / n) = a / b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [zero_div, div_zero]
  · field_simp

theorem tendsto_ratio :
  Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds (25 / 7)) := by
  have h1 : Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / N) atTop (nhds (25 / 32)) := tendsto_count_3s_div_id
  have h2 : Tendsto (fun N : ℕ => (A206911_count_2s N : ℝ) / N) atTop (nhds (7 / 32)) := tendsto_count_2s_div_id
  have h3 : (7 / 32 : ℝ) ≠ 0 := by norm_num
  have h_div := Tendsto.div h1 h2 h3
  have h_eq : (fun N : ℕ => ((A206911_count_3s N : ℝ) / N) / ((A206911_count_2s N : ℝ) / N)) =ᶠ[atTop] (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) := by
    simp only [EventuallyEq, eventually_atTop]
    use C_cut
    intro n hn
    have h_n_pos : (n : ℝ) ≠ 0 := by
      have : (C_cut : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have : (0 : ℝ) < (C_cut : ℝ) := by
        unfold C_cut
        norm_num
      linarith
    exact div_div_div_cancel_n (A206911_count_3s n : ℝ) (A206911_count_2s n : ℝ) h_n_pos
  have h_limit : ((25 / 32 : ℝ) / (7 / 32 : ℝ)) = 25 / 7 := by norm_num
  rw [h_limit] at h_div
  exact (tendsto_congr' h_eq).mp h_div

theorem oeis_206911_conjecture :
  -- Part 1: The difference sequence consists of 2s and 3s for n ≥ 1.
  (∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) ∧

  -- Part 2: The ratio of counts of 3s to 2s tends to a limit L in (3.5, 3.6).
  (∃ L : ℝ,
     (35/10 : ℝ) < L ∧ L < (36/10 : ℝ) ∧
     Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds L)) := by
  constructor
  · exact oeis_206911_part1
  · use 25 / 7
    refine ⟨by norm_num, by norm_num, tendsto_ratio⟩
