import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 500000

open Real Nat Finset Filter

/--
A206911: Position of $n$-th partial sum of the harmonic series when all the partial sums are jointly ranked with the set $\{\log(k+1)\}$; complement of A206912.
The $n$-th term $a(n)$ is the rank of $S(n) = \sum_{i=1}^n 1/i$ in the sorted list.
This rank is computed as $n + \lfloor \exp(S(n)) - 1 \rfloor$.
-/
noncomputable def A206911 (n : ℕ) : ℕ :=
  -- Define $S_n = \sum_{k=1}^n \frac{1}{k}$
  let S_n_real : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

  -- The number of log terms less than S_n is $\lfloor e^{S_n} - 1 \rfloor$.
  let count_log_terms : ℤ := floor (exp S_n_real - 1)

  -- Final rank: n + count.
  n + count_log_terms.toNat

noncomputable def S_real (n : ℕ) : ℝ :=
  (range n).sum fun k => 1 / ((k : ℝ) + 1)

lemma A206911_eq (n : ℕ) : (A206911 n : ℤ) = (n : ℤ) + (Nat.floor (exp (S_real n) - 1) : ℤ) := by
  rfl

-- Formalization of the conjecture.

/-- The difference sequence of A206911. Always an integer, should be 2 or 3 based on the conjecture. -/
noncomputable def A206911_diff (n : ℕ) : ℤ :=
  (A206911 (n + 1) : ℤ) - (A206911 n : ℤ)

/-- The number of times the difference sequence is 3, for indices $k \in \{1, \dots, N\}$. -/
noncomputable def count_threes (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

/-- The number of terms considered is $N$. Assuming the difference is 2 or 3 for all $k \in \{1, \dots, N\}$,
the number of 2s is $N$ minus the number of 3s. -/
noncomputable def count_twos (N : ℕ) : ℕ :=
  N - count_threes N

/-- The ratio of the number of 3s to the number of 2s in the difference sequence up to index $N$. -/
noncomputable def ratio_threes_to_twos (N : ℕ) : ℝ :=
  if count_twos N = 0 then 0
  else (count_threes N : ℝ) / (count_twos N : ℝ)

lemma S_real_succ (n : ℕ) : S_real (n + 1) = S_real n + 1 / ((n : ℝ) + 1) := by
  unfold S_real
  rw [sum_range_succ]

lemma log_step_upper (n : ℕ) (hn : 1 ≤ n) : 1 / ((n : ℝ) + 1) < Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
  have h1 : 0 < (n : ℝ) := by positivity
  have h2 : 0 < (n : ℝ) + 1 := by positivity
  rw [← log_div h2.ne' h1.ne']
  have h_div : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by
    field_simp
  rw [h_div]
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have hx : -(1 / ((n : ℝ) + 1)) ≠ 0 := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have h_add := Real.add_one_lt_exp hx
  have h_lhs : -(1 / ((n : ℝ) + 1)) + 1 = (n : ℝ) / ((n : ℝ) + 1) := by
    field_simp; try ring
  rw [h_lhs] at h_add
  rw [exp_neg] at h_add
  have h_inv : rexp (1 / ((n : ℝ) + 1)) < ((n : ℝ) + 1) / (n : ℝ) := by
    have h_pos1 : 0 < (n : ℝ) / ((n : ℝ) + 1) := by positivity
    have h_pos2 : 0 < rexp (1 / ((n : ℝ) + 1)) := exp_pos _
    rw [lt_inv_comm₀ h_pos1 h_pos2] at h_add
    have h_inv_eq : ((n : ℝ) / ((n : ℝ) + 1))⁻¹ = ((n : ℝ) + 1) / (n : ℝ) := by
      field_simp
    rwa [h_inv_eq] at h_add
  have h_rhs : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by
    field_simp
  rw [h_rhs] at h_inv
  exact h_inv

lemma S_real_sub_log_decreasing (n : ℕ) (hn : 1 ≤ n) :
    S_real (n + 1) - Real.log ((n : ℝ) + 1) < S_real n - Real.log (n : ℝ) := by
  have h_step := log_step_upper n hn
  rw [S_real_succ]
  linarith

lemma S_real_sub_log_le (n : ℕ) (hn : 5 ≤ n) :
    S_real n - Real.log (n : ℝ) ≤ S_real 5 - Real.log (5 : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have h_dec := S_real_sub_log_decreasing k (by linarith)
    push_cast at h_dec ⊢
    linarith

lemma exp_S_real_succ_sub_exp_lt_exp_sub_log (n : ℕ) :
    exp (S_real (n + 1)) - exp (S_real n) < exp (S_real (n + 1) - Real.log ((n : ℝ) + 1)) := by
  have h_eq : exp (S_real (n + 1)) - exp (S_real n) = exp (S_real (n + 1)) * (1 - exp (- (1 / ((n : ℝ) + 1)))) := by
    rw [S_real_succ n]
    rw [exp_add]
    have h_neg_add : exp (1 / ((n : ℝ) + 1)) * exp (-(1 / ((n : ℝ) + 1))) = 1 := by
      rw [← exp_add]
      have : 1 / ((n : ℝ) + 1) + -(1 / ((n : ℝ) + 1)) = 0 := by ring
      rw [this, exp_zero]
    calc exp (S_real n) * exp (1 / ((n : ℝ) + 1)) - exp (S_real n)
      _ = exp (S_real n) * exp (1 / ((n : ℝ) + 1)) - exp (S_real n) * 1 := by ring
      _ = exp (S_real n) * exp (1 / ((n : ℝ) + 1)) - exp (S_real n) * (exp (1 / ((n : ℝ) + 1)) * exp (-(1 / ((n : ℝ) + 1)))) := by rw [h_neg_add]
      _ = exp (S_real n) * exp (1 / ((n : ℝ) + 1)) * (1 - exp (-(1 / ((n : ℝ) + 1)))) := by ring
  rw [h_eq]
  have h_neg_ne : - (1 / ((n : ℝ) + 1)) ≠ 0 := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have h_add := Real.add_one_lt_exp h_neg_ne
  have h_lt : 1 - exp (- (1 / ((n : ℝ) + 1))) < 1 / ((n : ℝ) + 1) := by linarith
  have h_exp_pos : 0 < exp (S_real (n + 1)) := exp_pos _
  have h_mul : exp (S_real (n + 1)) * (1 - exp (- (1 / ((n : ℝ) + 1)))) < exp (S_real (n + 1)) * (1 / ((n : ℝ) + 1)) := by
    gcongr
  have h_rw : exp (S_real (n + 1)) * (1 / ((n : ℝ) + 1)) = exp (S_real (n + 1) - Real.log ((n : ℝ) + 1)) := by
    rw [exp_sub, exp_log (by positivity)]
    ring
  linarith

lemma exp_137_60_lt_ten : exp (137 / 60) < 10 := by
  have h_exp_one_lt : exp 1 < (27182818286 / 10000000000 : ℝ) := by
    have := exp_one_lt_d9
    linarith
  have h_y_nonneg : 0 ≤ (43 / 60 : ℝ) := by positivity
  have h_sum := Real.sum_le_exp_of_nonneg h_y_nonneg 4
  have h_sum_eq : ∑ i ∈ range 4, (43 / 60 : ℝ) ^ i / i ! = (2637127 / 1296000 : ℝ) := by
    simp_rw [sum_range_succ]
    ring
  rw [h_sum_eq] at h_sum
  have h_div_le : exp (137 / 60) ≤ (exp 1) ^ 3 / (2637127 / 1296000 : ℝ) := by
    have h_eq : exp (137 / 60) = (exp 1) ^ 3 / exp (43 / 60) := by
      have h_sub : (137 / 60 : ℝ) = 3 - 43 / 60 := by norm_num
      rw [h_sub, exp_sub]
      have h3 : (3 : ℝ) = 1 + 1 + 1 := by norm_num
      rw [h3, exp_add, exp_add]
      ring
    rw [h_eq]
    have h_pow_pos : 0 ≤ (exp 1) ^ 3 := by positivity
    have h_y_pos : (0 : ℝ) < 2637127 / 1296000 := by positivity
    exact div_le_div_of_nonneg_left h_pow_pos h_y_pos h_sum
  have h_pow_lt : (exp 1) ^ 3 < (27182818286 / 10000000000 : ℝ) ^ 3 := by
    gcongr
  have h_div_lt : (exp 1) ^ 3 / (2637127 / 1296000 : ℝ) < (27182818286 / 10000000000 : ℝ) ^ 3 / (2637127 / 1296000 : ℝ) := by
    have h_y_pos : (0 : ℝ) < 2637127 / 1296000 := by positivity
    exact div_lt_div_of_pos_right h_pow_lt h_y_pos
  have h_q_lt : ((27182818286 / 10000000000 : ℚ) ^ 3 / (2637127 / 1296000 : ℚ) : ℝ) < 10 := by
    exact_mod_cast (by norm_num : (27182818286 / 10000000000 : ℚ) ^ 3 / (2637127 / 1296000 : ℚ) < 10)
  have h_cast_div : (27182818286 / 10000000000 : ℝ) ^ 3 / (2637127 / 1296000 : ℝ) = (((27182818286 / 10000000000 : ℚ) ^ 3 / (2637127 / 1296000 : ℚ) : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast_div] at h_div_lt
  linarith

lemma exp_S_real_succ_sub_exp_lt_two (n : ℕ) (hn : 4 ≤ n) : exp (S_real (n + 1)) - exp (S_real n) < 2 := by
  have h_lt := exp_S_real_succ_sub_exp_lt_exp_sub_log n
  have h_le := S_real_sub_log_le (n + 1) (by linarith)
  have h_exp_le : exp (S_real (n + 1) - Real.log ((n : ℝ) + 1)) ≤ exp (S_real 5 - Real.log 5) := by
    push_cast at h_le ⊢
    exact exp_le_exp.mpr h_le
  have h_S5 : S_real 5 = 137 / 60 := by
    unfold S_real
    simp_rw [sum_range_succ]
    norm_num
  have h_S5_exp : exp (S_real 5 - Real.log 5) = exp (137 / 60) / 5 := by
    rw [h_S5, exp_sub, exp_log (by positivity)]
  have h_S5_lt : exp (S_real 5 - Real.log 5) < 2 := by
    rw [h_S5_exp]
    have h_ten := exp_137_60_lt_ten
    linarith
  linarith

lemma log_lt_sub_one {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) : Real.log y < y - 1 := by
  have h_ne : Real.log y ≠ 0 := by
    intro h
    have h_eq : exp (Real.log y) = exp 0 := by rw [h]
    rw [exp_log hy, exp_zero] at h_eq
    exact hy1 h_eq
  have h_exp := Real.add_one_lt_exp h_ne
  rw [exp_log hy] at h_exp
  linarith

lemma log_step_lower (n : ℕ) (hn : 1 ≤ n) : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) < 1 / ((n : ℝ) + 1) := by
  have h1 : 0 < (n : ℝ) + 1 := by positivity
  have h2 : 0 < (n : ℝ) + 2 := by positivity
  have hy : 0 < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by positivity
  have hy1 : ((n : ℝ) + 2) / ((n : ℝ) + 1) ≠ 1 := by
    intro h
    have : ((n : ℝ) + 2) = ((n : ℝ) + 1) := by
      rw [div_eq_iff h1.ne'] at h
      linarith
    linarith
  have h_lt := log_lt_sub_one hy hy1
  have h_div : ((n : ℝ) + 2) / ((n : ℝ) + 1) = 1 + 1 / ((n : ℝ) + 1) := by
    field_simp; try ring
  rw [h_div] at h_lt
  have h_log_div : Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) = Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) := by
    rw [log_div h2.ne' h1.ne']
  rw [h_div] at h_log_div
  rw [← h_log_div]
  linarith

lemma S_real_gt_log (n : ℕ) (hn : 1 ≤ n) : Real.log ((n : ℝ) + 1) < S_real n := by
  induction n, hn using Nat.le_induction with
  | base =>
    unfold S_real
    simp
    have h_log2 : Real.log (1 + 1) < 1 := by
      have : (1 : ℝ) + 1 = 2 := by norm_num
      rw [this]
      rw [Real.log_lt_iff_lt_exp (by positivity)]
      have : (2 : ℝ) < exp 1 := by
        have := exp_one_gt_d9
        linarith
      exact this
    exact h_log2
  | succ k hk ih =>
    rw [S_real_succ]
    have h_step := log_step_lower k hk
    have h_eq : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    push_cast at h_step ⊢
    rw [h_eq]
    linarith

lemma exp_S_real_succ_sub_exp_gt_one (n : ℕ) (hn : 1 ≤ n) : exp (S_real (n + 1)) - exp (S_real n) > 1 := by
  have h_n_pos : 0 < (n : ℝ) + 1 := by positivity
  have h_exp_S_gt : (n : ℝ) + 1 < exp (S_real n) := by
    have h_gt := S_real_gt_log n hn
    have h_exp_lt : exp (Real.log ((n : ℝ) + 1)) < exp (S_real n) := by
      rwa [Real.exp_lt_exp]
    rwa [exp_log h_n_pos] at h_exp_lt
  have h_step_gt : 1 / ((n : ℝ) + 1) < exp (1 / ((n : ℝ) + 1)) - 1 := by
    have h_ne : 1 / ((n : ℝ) + 1) ≠ 0 := by positivity
    have h_add := Real.add_one_lt_exp h_ne
    linarith
  have h_prod : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) < exp (S_real n) * (exp (1 / ((n : ℝ) + 1)) - 1) := by
    have h1 : 0 < (n : ℝ) + 1 := by positivity
    have h2 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h3 : 0 ≤ exp (S_real n) := by positivity
    have h4 : 0 ≤ exp (1 / ((n : ℝ) + 1)) - 1 := by linarith
    nlinarith
  have h_ring : exp (S_real (n + 1)) - exp (S_real n) = exp (S_real n) * (exp (1 / ((n : ℝ) + 1)) - 1) := by
    rw [S_real_succ n, exp_add]
    ring
  have h_div_eq : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
    field_simp
  rw [h_ring]
  rw [h_div_eq] at h_prod
  exact h_prod

lemma lt_of_pow_lt_pow {x y : ℝ} (hy : 0 ≤ y) (k : ℕ) (h : x ^ k < y ^ k) : x < y := by
  by_contra! h_le
  have h_pow : y ^ k ≤ x ^ k := by gcongr
  linarith

lemma exp_S_real_succ_sub_exp_lt_two_one : exp (S_real 2) - exp (S_real 1) < 2 := by
  have h_S1 : S_real 1 = 1 := by
    unfold S_real; simp
  have h_S2 : S_real 2 = 3 / 2 := by
    unfold S_real; simp_rw [sum_range_succ]
    norm_num
  have h_exp_one_lt : exp 1 < (27182818286 / 10000000000 : ℝ) := by
    have := exp_one_lt_d9
    linarith
  have h_exp_one_gt : (27182818283 / 10000000000 : ℝ) < exp 1 := by
    have := exp_one_gt_d9
    linarith
  have h_exp_32_lt : exp (3 / 2) < 9 / 2 := by
    apply lt_of_pow_lt_pow (by positivity) 2
    have h_pow_eq : exp (3 / 2) ^ 2 = exp 3 := by
      calc exp (3 / 2) ^ 2
        _ = exp (3 / 2) * exp (3 / 2) := by ring
        _ = exp (3 / 2 + 3 / 2) := by rw [← exp_add]
        _ = exp 3 := by
          have : (3 / 2 : ℝ) + 3 / 2 = 3 := by norm_num
          rw [this]
    rw [h_pow_eq]
    have h_exp3 : exp 3 = (exp 1) ^ 3 := by
      have h3 : (3 : ℝ) = (3 : ℕ) • (1 : ℝ) := by simp
      rw [h3, exp_nsmul]
    rw [h_exp3]
    have h_lt : (exp 1) ^ 3 < (27182818286 / 10000000000 : ℝ) ^ 3 := by
      gcongr
    have h_num : (27182818286 / 10000000000 : ℝ) ^ 3 < (9 / 2) ^ 2 := by
      norm_num
    linarith
  rw [h_S1, h_S2]
  linarith

lemma exp_S_real_succ_sub_exp_lt_two_two : exp (S_real 3) - exp (S_real 2) < 2 := by
  have h_S2 : S_real 2 = 3 / 2 := by
    unfold S_real; simp_rw [sum_range_succ]; norm_num
  have h_S3 : S_real 3 = 11 / 6 := by
    unfold S_real; simp_rw [sum_range_succ]; norm_num
  have h_exp_one_lt : exp 1 < (27182818286 / 10000000000 : ℝ) := by
    have := exp_one_lt_d9
    linarith
  have h_exp_one_gt : (27182818283 / 10000000000 : ℝ) < exp 1 := by
    have := exp_one_gt_d9
    linarith
  have h_exp_116_lt : exp (11 / 6) < 313 / 50 := by
    apply lt_of_pow_lt_pow (by positivity) 6
    have h_pow_eq : exp (11 / 6) ^ 6 = exp 11 := by
      calc exp (11 / 6) ^ 6
        _ = exp (11 / 6) * exp (11 / 6) * exp (11 / 6) * exp (11 / 6) * exp (11 / 6) * exp (11 / 6) := by ring
        _ = exp (11 / 6 + 11 / 6 + 11 / 6 + 11 / 6 + 11 / 6 + 11 / 6) := by rw [← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
        _ = exp 11 := by
          have : (11 / 6 : ℝ) + 11 / 6 + 11 / 6 + 11 / 6 + 11 / 6 + 11 / 6 = 11 := by norm_num
          rw [this]
    rw [h_pow_eq]
    have h_exp11 : exp 11 = (exp 1) ^ 11 := by
      have h11 : (11 : ℝ) = (11 : ℕ) • (1 : ℝ) := by simp
      rw [h11, exp_nsmul]
    rw [h_exp11]
    have h_lt : (exp 1) ^ 11 < (27182818286 / 10000000000 : ℝ) ^ 11 := by
      gcongr
    have h_num : (27182818286 / 10000000000 : ℝ) ^ 11 < (313 / 50 : ℝ) ^ 6 := by
      norm_num
    linarith
  have h_exp_32_gt : (447 / 100 : ℝ) < exp (3 / 2) := by
    apply lt_of_pow_lt_pow (by positivity) 2
    have h_pow_eq : exp (3 / 2) ^ 2 = exp 3 := by
      calc exp (3 / 2) ^ 2
        _ = exp (3 / 2) * exp (3 / 2) := by ring
        _ = exp (3 / 2 + 3 / 2) := by rw [← exp_add]
        _ = exp 3 := by
          have : (3 / 2 : ℝ) + 3 / 2 = 3 := by norm_num
          rw [this]
    rw [h_pow_eq]
    have h_exp3 : exp 3 = (exp 1) ^ 3 := by
      have h3 : (3 : ℝ) = (3 : ℕ) • (1 : ℝ) := by simp
      rw [h3, exp_nsmul]
    rw [h_exp3]
    have h_lt : (27182818283 / 10000000000 : ℝ) ^ 3 < (exp 1) ^ 3 := by
      gcongr
    have h_num : (447 / 100 : ℝ) ^ 2 < (27182818283 / 10000000000 : ℝ) ^ 3 := by
      norm_num
    linarith
  rw [h_S2, h_S3]
  linarith

lemma exp_S_real_succ_sub_exp_lt_two_three : exp (S_real 4) - exp (S_real 3) < 2 := by
  have h_S3 : S_real 3 = 11 / 6 := by
    unfold S_real; simp_rw [sum_range_succ]; norm_num
  have h_S4 : S_real 4 = 25 / 12 := by
    unfold S_real; simp_rw [sum_range_succ]; norm_num
  have h_exp_one_lt : exp 1 < (27182818286 / 10000000000 : ℝ) := by
    have := exp_one_lt_d9
    linarith
  have h_exp_one_gt : (27182818283 / 10000000000 : ℝ) < exp 1 := by
    have := exp_one_gt_d9
    linarith
  have h_exp_2512_lt : exp (25 / 12) < 804 / 100 := by
    apply lt_of_pow_lt_pow (by positivity) 12
    have h_pow_eq : exp (25 / 12) ^ 12 = exp 25 := by
      calc exp (25 / 12) ^ 12
        _ = exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) * exp (25 / 12) := by ring
        _ = exp (25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12) := by rw [← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
        _ = exp 25 := by
          have : (25 / 12 : ℝ) + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 + 25 / 12 = 25 := by norm_num
          rw [this]
    rw [h_pow_eq]
    have h_exp25 : exp 25 = (exp 1) ^ 25 := by
      have h25 : (25 : ℝ) = (25 : ℕ) • (1 : ℝ) := by simp
      rw [h25, exp_nsmul]
    rw [h_exp25]
    have h_lt : (exp 1) ^ 25 < (27182818286 / 10000000000 : ℝ) ^ 25 := by
      gcongr
    have h_num : (27182818286 / 10000000000 : ℝ) ^ 25 < (804 / 100 : ℝ) ^ 12 := by
      norm_num
    linarith
  have h_exp_116_gt : (31 / 5 : ℝ) < exp (11 / 6) := by
    apply lt_of_pow_lt_pow (by positivity) 6
    have h_pow_eq : exp (11 / 6) ^ 6 = exp 11 := by
      calc exp (11 / 6) ^ 6
        _ = exp (11 / 6) * exp (11 / 6) * exp (11 / 6) * exp (11 / 6) * exp (11 / 6) * exp (11 / 6) := by ring
        _ = exp (11 / 6 + 11 / 6 + 11 / 6 + 11 / 6 + 11 / 6 + 11 / 6) := by rw [← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
        _ = exp 11 := by
          have : (11 / 6 : ℝ) + 11 / 6 + 11 / 6 + 11 / 6 + 11 / 6 + 11 / 6 = 11 := by norm_num
          rw [this]
    rw [h_pow_eq]
    have h_exp11 : exp 11 = (exp 1) ^ 11 := by
      have h11 : (11 : ℝ) = (11 : ℕ) • (1 : ℝ) := by simp
      rw [h11, exp_nsmul]
    rw [h_exp11]
    have h_lt : (27182818283 / 10000000000 : ℝ) ^ 11 < (exp 1) ^ 11 := by
      gcongr
    have h_num : (31 / 5 : ℝ) ^ 6 < (27182818283 / 10000000000 : ℝ) ^ 11 := by
      norm_num
    linarith
  rw [h_S3, h_S4]
  linarith

lemma exp_S_real_succ_sub_exp_lt_two_all (n : ℕ) (hn : 1 ≤ n) : exp (S_real (n + 1)) - exp (S_real n) < 2 := by
  rcases lt_or_ge n 4 with h_lt | h_ge
  · interval_cases n
    · exact exp_S_real_succ_sub_exp_lt_two_one
    · exact exp_S_real_succ_sub_exp_lt_two_two
    · exact exp_S_real_succ_sub_exp_lt_two_three
  · exact exp_S_real_succ_sub_exp_lt_two n h_ge

lemma floor_diff_of_diff_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h1 : 1 < x - y) (h2 : x - y < 2) :
    (Nat.floor x : ℤ) - (Nat.floor y : ℤ) = 1 ∨ (Nat.floor x : ℤ) - (Nat.floor y : ℤ) = 2 := by
  have hx_le : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
  have hx_gt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  have hy_le : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hy
  have hy_gt : y < (Nat.floor y : ℝ) + 1 := Nat.lt_floor_add_one y
  have h_ge : 1 < (Nat.floor x : ℝ) - (Nat.floor y : ℝ) + 1 := by linarith
  have h_le : (Nat.floor x : ℝ) - (Nat.floor y : ℝ) - 1 < 2 := by linarith
  have h_ge_int : 0 < (Nat.floor x : ℤ) - (Nat.floor y : ℤ) := by
    exact_mod_cast (by linarith : 0 < (Nat.floor x : ℝ) - (Nat.floor y : ℝ))
  have h_le_int : (Nat.floor x : ℤ) - (Nat.floor y : ℤ) < 3 := by
    exact_mod_cast (by linarith : (Nat.floor x : ℝ) - (Nat.floor y : ℝ) < 3)
  omega

lemma harmonic_cast (n : ℕ) : (harmonic n : ℝ) = S_real n := by
  unfold harmonic S_real
  push_cast
  congr 1
  ext x
  exact inv_eq_one_div ((x : ℝ) + 1)

lemma exp_eulerMascheroni_bounds : 16 / 9 < exp eulerMascheroniConstant ∧ exp eulerMascheroniConstant < 41 / 23 := by
  have h_S615 : S_real 615 = harmonic 615 := by
    rw [harmonic_cast]
  have h_H_val : (harmonic 615 : ℝ) < 7 := by
    exact_mod_cast (by norm_num : (harmonic 615 : ℚ) < 7)
  have h_H_pos : 0 < (harmonic 615 : ℝ) := by
    exact_mod_cast (by norm_num : 0 < (harmonic 615 : ℚ))
  let y : ℝ := 7 - (harmonic 615 : ℝ)
  have hy_pos : 0 < y := by
    dsimp [y]; linarith
  have hy_lt1 : y < 1 := by
    dsimp [y]
    have : (6 : ℝ) < harmonic 615 := by
      exact_mod_cast (by norm_num : (6 : ℚ) < harmonic 615)
    linarith
  have h_exp_neg_y : 1 - y < exp (-y) := by
    have h_ne : -y ≠ 0 := by linarith
    have h := Real.add_one_lt_exp h_ne
    linarith
  have h_exp_y : 1 + y < exp y := by
    have h_ne : y ≠ 0 := by linarith
    have h := Real.add_one_lt_exp h_ne
    linarith
  have h_inv_exp_y : exp (-y) < 1 / (1 + y) := by
    rw [exp_neg, one_div]
    have h_pos : 0 < (1 : ℝ) + y := by linarith
    have h_pos2 : 0 < exp y := exp_pos _
    rwa [inv_lt_inv₀ h_pos2 h_pos]
  have h_exp7 : exp 7 = (exp 1) ^ 7 := by
    have h7 : (7 : ℝ) = (7 : ℕ) • (1 : ℝ) := by simp
    rw [h7, exp_nsmul]
  have h_exp_H_gt : (exp 1) ^ 7 * (1 - y) < exp (harmonic 615 : ℝ) := by
    have h_mul : exp 7 * (1 - y) < exp 7 * exp (-y) := by
      exact mul_lt_mul_of_pos_left h_exp_neg_y (exp_pos 7)
    rw [← exp_add] at h_mul
    have h_eq : (7 : ℝ) + -y = harmonic 615 := by
      dsimp [y]; ring
    rw [h_eq, h_exp7] at h_mul
    exact h_mul
  have h_exp_H_lt : exp (harmonic 615 : ℝ) < (exp 1) ^ 7 / (1 + y) := by
    have h_mul : exp 7 * exp (-y) < exp 7 * (1 / (1 + y)) := by
      exact mul_lt_mul_of_pos_left h_inv_exp_y (exp_pos 7)
    rw [← exp_add] at h_mul
    have h_eq : (7 : ℝ) + -y = harmonic 615 := by
      dsimp [y]; ring
    rw [h_eq] at h_mul
    have h_div : exp 7 * (1 / (1 + y)) = exp 7 / (1 + y) := by ring
    rw [h_div, h_exp7] at h_mul
    exact h_mul
  have h_exp_one_lt : exp 1 < (27182818286 / 10000000000 : ℝ) := by
    have := exp_one_lt_d9
    linarith
  have h_exp_one_gt : (27182818283 / 10000000000 : ℝ) < exp 1 := by
    have := exp_one_gt_d9
    linarith
  have h_gt : 16 / 9 < exp (harmonic 615 : ℝ) / 616 := by
    have h_pow_gt : (27182818283 / 10000000000 : ℝ) ^ 7 * ↑(harmonic 615 - 6 : ℚ) < (exp 1) ^ 7 * (1 - y) := by
      have h_eq : 1 - y = ↑(harmonic 615 - 6 : ℚ) := by
        dsimp [y]; push_cast; ring
      rw [h_eq]
      gcongr
      dsimp [y]; linarith
    have h_combined := lt_trans h_pow_gt h_exp_H_gt
    have h_num : (16 / 9 : ℝ) < (27182818283 / 10000000000 : ℝ) ^ 7 * ((harmonic 615 - 6 : ℚ) : ℝ) / 616 := by
      norm_num
    linarith
  have h_lt : exp (harmonic 615 : ℝ) / 615 < 41 / 23 := by
    have h_pow_lt : (exp 1) ^ 7 / (1 + y) < (27182818286 / 10000000000 : ℝ) ^ 7 / ↑(8 - harmonic 615 : ℚ) := by
      have h_eq : 1 + y = ↑(8 - harmonic 615 : ℚ) := by
        dsimp [y]; push_cast; ring
      rw [h_eq]
      gcongr
      · linarith
    have h_combined := lt_trans h_exp_H_lt h_pow_lt
    have h_num : (27182818286 / 10000000000 : ℝ) ^ 7 / ((8 - harmonic 615 : ℚ) : ℝ) / 615 < 41 / 23 := by
      norm_num
    linarith
  have h_seq_lt := eulerMascheroniSeq_lt_eulerMascheroniConstant 615
  have h_lt_seq := eulerMascheroniConstant_lt_eulerMascheroniSeq' 615
  rw [eulerMascheroniSeq] at h_seq_lt
  rw [eulerMascheroniSeq'] at h_lt_seq
  have h_ne_zero : (615 : ℕ) ≠ 0 := by decide
  rw [if_neg h_ne_zero] at h_lt_seq
  have h_616_eq : ((615 : ℕ) : ℝ) + 1 = 616 := by norm_num
  rw [h_616_eq] at h_seq_lt
  have h_exp_lt_exp1 : exp (harmonic 615 - Real.log 616) < exp eulerMascheroniConstant := by
    rw [exp_lt_exp]
    exact h_seq_lt
  have h_exp_lt_exp2 : exp eulerMascheroniConstant < exp (harmonic 615 - Real.log 615) := by
    rw [exp_lt_exp]
    exact h_lt_seq
  rw [exp_sub, exp_log (by positivity)] at h_exp_lt_exp1
  rw [exp_sub, exp_log (by positivity)] at h_exp_lt_exp2
  constructor
  · exact lt_trans h_gt h_exp_lt_exp1
  · exact lt_trans h_exp_lt_exp2 h_lt

lemma diff_ge_two_and_le_three (n : ℕ) (hn : 1 ≤ n) : A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  unfold A206911_diff
  rw [A206911_eq (n + 1), A206911_eq n]
  push_cast
  have h_exp_S_gt1 := exp_S_real_succ_sub_exp_gt_one n hn
  have h_exp_S_lt2 := exp_S_real_succ_sub_exp_lt_two_all n hn
  have h_exp_S_n_nonneg : 0 ≤ exp (S_real n) - 1 := by
    have h_S_n_nonneg : 0 ≤ S_real n := by
      unfold S_real; positivity
    have h_exp_gt := Real.one_le_exp h_S_n_nonneg
    linarith
  have h_exp_S_n1_nonneg : 0 ≤ exp (S_real (n + 1)) - 1 := by
    have h_S_n1_nonneg : 0 ≤ S_real (n + 1) := by
      unfold S_real; positivity
    have h_exp_gt := Real.one_le_exp h_S_n1_nonneg
    linarith
  have h_diff_bounds := floor_diff_of_diff_bounds h_exp_S_n1_nonneg h_exp_S_n_nonneg (by linarith) (by linarith)
  omega


lemma S_real_eq_harmonic (n : ℕ) : S_real n = (harmonic n : ℝ) := by
  induction n with
  | zero =>
    unfold S_real harmonic
    simp
  | succ n ih =>
    rw [S_real_succ, ih]
    unfold harmonic
    rw [sum_range_succ]
    push_cast
    ring


lemma tendsto_S_real_sub_log : Tendsto (fun n ↦ S_real n - Real.log n) atTop (nhds eulerMascheroniConstant) := by
  have h := tendsto_harmonic_sub_log
  simp_rw [← S_real_eq_harmonic] at h
  exact h


lemma tendsto_exp_S_real_div_n : Tendsto (fun n ↦ exp (S_real n) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h1 : Tendsto (fun n ↦ exp (S_real n - Real.log n)) atTop (nhds (exp eulerMascheroniConstant)) := by
    exact (continuous_exp.tendsto eulerMascheroniConstant).comp tendsto_S_real_sub_log
  have h_eq : (fun n ↦ exp (S_real n - Real.log n)) =ᶠ[atTop] (fun n ↦ exp (S_real n) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : 0 < (n : ℝ) := by positivity
    rw [exp_sub, exp_log hn_pos]
  exact (tendsto_congr' h_eq).mp h1


lemma floor_bounds (x : ℝ) (hx : 0 ≤ x) : x - 1 < (Nat.floor x : ℝ) ∧ (Nat.floor x : ℝ) ≤ x := by
  constructor
  · linarith [lt_floor_add_one x]
  · exact floor_le hx



lemma tendsto_g : Tendsto (fun n ↦ (exp (S_real n) - 2) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h_eq : (fun n ↦ (exp (S_real n) - 2) / (n : ℝ)) = (fun n ↦ exp (S_real n) / (n : ℝ) - 2 / (n : ℝ)) := by
    ext n
    ring
  rw [h_eq]
  have h1 := tendsto_exp_S_real_div_n
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have h3 := Tendsto.sub h1 h2
  rw [sub_zero] at h3
  exact h3

lemma tendsto_h : Tendsto (fun n ↦ (exp (S_real n) - 1) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h_eq : (fun n ↦ (exp (S_real n) - 1) / (n : ℝ)) = (fun n ↦ exp (S_real n) / (n : ℝ) - 1 / (n : ℝ)) := by
    ext n
    ring
  rw [h_eq]
  have h1 := tendsto_exp_S_real_div_n
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have h3 := Tendsto.sub h1 h2
  rw [sub_zero] at h3
  exact h3

lemma tendsto_floor_S_real_div_n : Tendsto (fun n ↦ (Nat.floor (exp (S_real n) - 1) : ℝ) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h_le1 : ∀ᶠ n in atTop, (exp (S_real n) - 2) / (n : ℝ) ≤ (Nat.floor (exp (S_real n) - 1) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : 0 < (n : ℝ) := by positivity
    have h_exp_S_nonneg : 0 ≤ S_real n := by
      unfold S_real; positivity
    have h_exp_S_gt1 : 1 ≤ exp (S_real n) := Real.one_le_exp h_exp_S_nonneg
    have hx_nonneg : 0 ≤ exp (S_real n) - 1 := by linarith
    have hb := floor_bounds (exp (S_real n) - 1) hx_nonneg
    gcongr
    linarith
  have h_le2 : ∀ᶠ n in atTop, (Nat.floor (exp (S_real n) - 1) : ℝ) / (n : ℝ) ≤ (exp (S_real n) - 1) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : 0 < (n : ℝ) := by positivity
    have h_exp_S_nonneg : 0 ≤ S_real n := by
      unfold S_real; positivity
    have h_exp_S_gt1 : 1 ≤ exp (S_real n) := Real.one_le_exp h_exp_S_nonneg
    have hx_nonneg : 0 ≤ exp (S_real n) - 1 := by linarith
    have hb := floor_bounds (exp (S_real n) - 1) hx_nonneg
    gcongr
    exact hb.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_g tendsto_h h_le1 h_le2

lemma tendsto_succ_div_self : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ) / (N : ℝ)) atTop (nhds 1) := by
  have h_eq : (fun N : ℕ ↦ (N + 1 : ℝ) / (N : ℝ)) =ᶠ[atTop] (fun N : ℕ ↦ 1 + 1 / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN_real : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have h_lim : Tendsto (fun N : ℕ ↦ 1 + 1 / (N : ℝ)) atTop (nhds 1) := by
    have h1 : Tendsto (fun N : ℕ ↦ 1 / (N : ℝ)) atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    have h2 := Tendsto.const_add 1 h1
    rw [add_zero] at h2
    exact h2
  exact (tendsto_congr' h_eq).mpr h_lim


lemma tendsto_floor_S_real_succ_div_N :
    Tendsto (fun N : ℕ ↦ (Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) / (N : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h_shift := tendsto_floor_S_real_div_n.comp (tendsto_add_atTop_nat 1)
  have h_mul := Tendsto.mul h_shift tendsto_succ_div_self
  dsimp only [Function.comp_apply] at h_mul
  simp_rw [Nat.cast_add_one] at h_mul
  rw [mul_one] at h_mul
  have h_eq : (fun N : ℕ ↦ ((Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) / (N + 1 : ℝ)) * ((N + 1 : ℝ) / (N : ℝ))) =ᶠ[atTop]
              (fun N : ℕ ↦ (Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1_real : (N : ℝ) + 1 ≠ 0 := by positivity
    have hN_real : (N : ℝ) ≠ 0 := by positivity
    calc ((Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) / (N + 1 : ℝ)) * ((N + 1 : ℝ) / (N : ℝ))
      _ = (Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) * (1 / (N + 1 : ℝ)) * ((N + 1 : ℝ) * (1 / (N : ℝ))) := by ring
      _ = (Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) * (1 / (N : ℝ)) * ((1 / (N + 1 : ℝ)) * ((N + 1 : ℝ))) := by ring
      _ = (Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) * (1 / (N : ℝ)) * 1 := by rw [one_div_mul_cancel hN1_real]
      _ = (Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) / (N : ℝ) := by ring
  exact (tendsto_congr' h_eq).mp h_mul


lemma sum_threes_to_twos_eq (N : ℕ) :
    (count_threes N : ℤ) = (A206911 (N + 1) : ℤ) - (A206911 1 : ℤ) - 2 * (N : ℤ) := by
  induction N with
  | zero =>
    unfold count_threes
    simp
  | succ n ih =>
    unfold count_threes at ih ⊢
    rw [sum_range_succ]
    rw [Nat.cast_add]
    rw [ih]
    push_cast
    have h_diff : (A206911 (n + 1 + 1) : ℤ) = (A206911 (n + 1) : ℤ) + A206911_diff (n + 1) := by
      unfold A206911_diff
      omega
    rw [h_diff]
    have h_bounds : A206911_diff (n + 1) = 2 ∨ A206911_diff (n + 1) = 3 := by
      apply diff_ge_two_and_le_three (n + 1)
      omega
    rcases h_bounds with h2 | h3
    · rw [h2]
      simp
      ring
    · rw [h3]
      simp
      ring

lemma tendsto_A206911_succ_div_N : Tendsto (fun N : ℕ ↦ (A206911 (N + 1) : ℝ) / (N : ℝ)) atTop (nhds (1 + exp eulerMascheroniConstant)) := by
  have h_eq : (fun N : ℕ ↦ (A206911 (N + 1) : ℝ) / (N : ℝ)) =ᶠ[atTop] (fun N : ℕ ↦ (N + 1 : ℝ) / (N : ℝ) + (Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN_real : (N : ℝ) ≠ 0 := by positivity
    have h_cast : (A206911 (N + 1) : ℝ) = (N + 1 : ℝ) + (Nat.floor (exp (S_real (N + 1)) - 1) : ℝ) := by
      have h1 := congr_arg (fun x : ℤ ↦ (x : ℝ)) (A206911_eq (N + 1))
      push_cast at h1
      exact h1
    rw [h_cast]
    ring
  have h_lim := Tendsto.add tendsto_succ_div_self tendsto_floor_S_real_succ_div_N
  exact (tendsto_congr' h_eq).mpr h_lim

lemma tendsto_count_threes_div_N :
    Tendsto (fun N : ℕ ↦ (count_threes N : ℝ) / (N : ℝ)) atTop (nhds (exp eulerMascheroniConstant - 1)) := by
  have h_eq : (fun N : ℕ ↦ (count_threes N : ℝ) / (N : ℝ)) =ᶠ[atTop]
              (fun N : ℕ ↦ (A206911 (N + 1) : ℝ) / (N : ℝ) - (A206911 1 : ℝ) / (N : ℝ) - 2) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN_real : (N : ℝ) ≠ 0 := by positivity
    have h_threes : (count_threes N : ℝ) = (A206911 (N + 1) : ℝ) - (A206911 1 : ℝ) - 2 * (N : ℝ) := by
      have h1 := sum_threes_to_twos_eq N
      have h2 := congr_arg (fun x : ℤ ↦ (x : ℝ)) h1
      push_cast at h2
      exact h2
    rw [h_threes]
    field_simp; try ring
  have h1 : Tendsto (fun N : ℕ ↦ (A206911 (N + 1) : ℝ) / (N : ℝ)) atTop (nhds (1 + exp eulerMascheroniConstant)) := tendsto_A206911_succ_div_N
  have h2 : Tendsto (fun N : ℕ ↦ (A206911 1 : ℝ) / (N : ℝ)) atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat (A206911 1 : ℝ)
  have h3 := Tendsto.sub h1 h2
  have h4 := h3.sub_const 2
  have h_lim : Tendsto (fun N : ℕ ↦ (A206911 (N + 1) : ℝ) / (N : ℝ) - (A206911 1 : ℝ) / (N : ℝ) - 2) atTop (nhds (exp eulerMascheroniConstant - 1)) := by
    have h_eq_limit : 1 + exp eulerMascheroniConstant - 0 - 2 = exp eulerMascheroniConstant - 1 := by ring
    rw [h_eq_limit] at h4
    exact h4
  exact (tendsto_congr' h_eq).mpr h_lim



lemma count_threes_le_self (N : ℕ) : count_threes N ≤ N := by
  induction N with
  | zero =>
    unfold count_threes
    simp
  | succ n ih =>
    unfold count_threes at ih ⊢
    rw [sum_range_succ]
    have : (if A206911_diff (n + 1) = 3 then 1 else 0) ≤ 1 := by
      split_ifs <;> omega
    omega

lemma tendsto_count_twos_div_N :
    Tendsto (fun N : ℕ ↦ (count_twos N : ℝ) / (N : ℝ)) atTop (nhds (2 - exp eulerMascheroniConstant)) := by
  have h_eq : (fun N : ℕ ↦ (count_twos N : ℝ) / (N : ℝ)) =ᶠ[atTop]
              (fun N : ℕ ↦ 3 - (A206911 (N + 1) : ℝ) / (N : ℝ) + (A206911 1 : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN_real : (N : ℝ) ≠ 0 := by positivity
    unfold count_twos
    rw [Nat.cast_sub (count_threes_le_self N)]
    have h_threes : (count_threes N : ℝ) = (A206911 (N + 1) : ℝ) - (A206911 1 : ℝ) - 2 * (N : ℝ) := by
      have h1 := sum_threes_to_twos_eq N
      have h2 := congr_arg (fun x : ℤ ↦ (x : ℝ)) h1
      push_cast at h2
      exact h2
    rw [h_threes]
    field_simp; try ring
  have h1 : Tendsto (fun N : ℕ ↦ (A206911 (N + 1) : ℝ) / (N : ℝ)) atTop (nhds (1 + exp eulerMascheroniConstant)) := tendsto_A206911_succ_div_N
  have h2 : Tendsto (fun N : ℕ ↦ (A206911 1 : ℝ) / (N : ℝ)) atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat (A206911 1 : ℝ)
  have h3 : Tendsto (fun N : ℕ ↦ 3 - (A206911 (N + 1) : ℝ) / (N : ℝ)) atTop (nhds (2 - exp eulerMascheroniConstant)) := by
    have h_const : Tendsto (fun N : ℕ ↦ (3 : ℝ)) atTop (nhds 3) := tendsto_const_nhds
    have h_sub := Tendsto.sub h_const h1
    have h_eq_limit : (3 : ℝ) - (1 + exp eulerMascheroniConstant) = 2 - exp eulerMascheroniConstant := by ring
    rw [h_eq_limit] at h_sub
    exact h_sub
  have h4 := Tendsto.add h3 h2
  have h_lim : Tendsto (fun N : ℕ ↦ 3 - (A206911 (N + 1) : ℝ) / (N : ℝ) + (A206911 1 : ℝ) / (N : ℝ)) atTop (nhds (2 - exp eulerMascheroniConstant)) := by
    rw [add_zero] at h4
    exact h4
  exact (tendsto_congr' h_eq).mpr h_lim



noncomputable def l_const : ℝ :=
  (exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant)

lemma l_const_bounds : 3.5 < l_const ∧ l_const < 3.6 := by
  have h_denom : 0 < 2 - exp eulerMascheroniConstant := by
    have : exp eulerMascheroniConstant < 41 / 23 := exp_eulerMascheroni_bounds.2
    linarith
  constructor
  · unfold l_const
    rw [lt_div_iff₀ h_denom]
    have : exp eulerMascheroniConstant > 16 / 9 := exp_eulerMascheroni_bounds.1
    linarith
  · unfold l_const
    rw [div_lt_iff₀ h_denom]
    have : exp eulerMascheroniConstant < 41 / 23 := exp_eulerMascheroni_bounds.2
    linarith

lemma tendsto_ratio_threes_to_twos :
    Tendsto ratio_threes_to_twos atTop (nhds l_const) := by
  have h_denom_pos : 0 < 2 - exp eulerMascheroniConstant := by
    have : exp eulerMascheroniConstant < 41 / 23 := exp_eulerMascheroni_bounds.2
    linarith
  have h_twos_eventually_pos : ∀ᶠ N in atTop, 0 < (count_twos N : ℝ) := by
    have h_lim := tendsto_count_twos_div_N
    have h_pos : 0 < (2 - exp eulerMascheroniConstant) / 2 := by linarith
    have h_mem : (2 - exp eulerMascheroniConstant) ∈ Set.Ioi ((2 - exp eulerMascheroniConstant) / 2) := by
      rw [Set.mem_Ioi]
      linarith
    have h_lt := tendsto_nhds.mp h_lim (Set.Ioi ((2 - exp eulerMascheroniConstant) / 2)) (isOpen_Ioi) h_mem
    filter_upwards [h_lt, eventually_ge_atTop 1] with N hN hn
    have hn_pos : 0 < (N : ℝ) := by positivity
    rw [Set.mem_preimage, Set.mem_Ioi] at hN
    have h_div_pos : 0 < (count_twos N : ℝ) / (N : ℝ) := by linarith
    have h_eq_twos : (count_twos N : ℝ) = ((count_twos N : ℝ) / (N : ℝ)) * (N : ℝ) := by
      field_simp
    rw [h_eq_twos]
    positivity
  have h_ratio_eq : ratio_threes_to_twos =ᶠ[atTop] (fun N ↦ (count_threes N : ℝ) / (count_twos N : ℝ)) := by
    filter_upwards [h_twos_eventually_pos] with N hN
    unfold ratio_threes_to_twos
    have h_ne : count_twos N ≠ 0 := by
      intro h
      have : (count_twos N : ℝ) = 0 := by exact_mod_cast h
      linarith
    rw [if_neg h_ne]
  have h_div_N_eq : (fun N ↦ (count_threes N : ℝ) / (count_twos N : ℝ)) =ᶠ[atTop]
                    (fun N ↦ ((count_threes N : ℝ) / (N : ℝ)) / ((count_twos N : ℝ) / (N : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN_real : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have h_lim_div : Tendsto (fun N ↦ ((count_threes N : ℝ) / (N : ℝ)) / ((count_twos N : ℝ) / (N : ℝ))) atTop
                           (nhds ((exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant))) := by
    apply Tendsto.div tendsto_count_threes_div_N tendsto_count_twos_div_N
    linarith
  have h_ratio_lim : Tendsto (fun N ↦ (count_threes N : ℝ) / (count_twos N : ℝ)) atTop (nhds l_const) := by
    change Tendsto (fun N ↦ (count_threes N : ℝ) / (count_twos N : ℝ)) atTop (nhds ((exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant)))
    exact (tendsto_congr' h_div_N_eq).mpr h_lim_div
  exact (tendsto_congr' h_ratio_eq).mpr h_ratio_lim





theorem oeis_a206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n ∈ ({2, 3} : Set ℤ)) ∧
  (∃ l : ℝ,
    3.5 < l ∧ l < 3.6 ∧
    Tendsto ratio_threes_to_twos atTop (nhds l)) := by
  constructor
  · intro n hn
    have h := diff_ge_two_and_le_three n hn
    rcases h with h2 | h3
    · rw [h2]; simp
    · rw [h3]; simp
  · use l_const
    refine ⟨l_const_bounds.1, l_const_bounds.2, ?_⟩
    exact tendsto_ratio_threes_to_twos
