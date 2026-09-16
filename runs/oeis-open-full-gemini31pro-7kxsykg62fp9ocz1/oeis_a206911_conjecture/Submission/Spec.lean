import FormalConjectures.Util.ProblemImports

open Real Nat Finset Filter

noncomputable def A206911 (n : ℕ) : ℕ :=
  let S_n_real : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)
  let count_log_terms : ℤ := floor (exp S_n_real - 1)
  n + count_log_terms.toNat

noncomputable def A206911_diff (n : ℕ) : ℤ :=
  (A206911 (n + 1) : ℤ) - (A206911 n : ℤ)

noncomputable def count_threes (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

noncomputable def count_twos (N : ℕ) : ℕ :=
  N - count_threes N

noncomputable def ratio_threes_to_twos (N : ℕ) : ℝ :=
  if count_twos N = 0 then 0
  else (count_threes N : ℝ) / (count_twos N : ℝ)



def H_rat (n : ℕ) : ℚ := (range n).sum fun k => 1 / (k + 1 : ℚ)
def taylor_sum (x : ℚ) (n : ℕ) : ℚ := (range n).sum fun k => x^k / (Nat.factorial k : ℚ)
def taylor_rem (x : ℚ) (n : ℕ) : ℚ := x^n * (n + 1 : ℚ) / (Nat.factorial n * n : ℚ)
def taylor_upper (x : ℚ) (n : ℕ) : ℚ := taylor_sum x n + taylor_rem x n

lemma H_rat_eq_harmonic (n : ℕ) : (H_rat n : ℝ) = harmonic n := by
  unfold H_rat harmonic
  push_cast
  apply sum_congr rfl
  intro x _
  rw [one_div]

lemma lower_bound_eval : ((16/9 : ℚ) : ℝ) < (((taylor_sum (H_rat 300 / 8) 8)^8 / 301 : ℚ) : ℝ) := by
  have h : (16/9 : ℚ) < (taylor_sum (H_rat 300 / 8) 8)^8 / 301 := by norm_num [taylor_sum, H_rat]
  exact_mod_cast h

lemma upper_bound_eval : (((taylor_upper (H_rat 580 / 8) 15)^8 / 580 : ℚ) : ℝ) < ((41/23 : ℚ) : ℝ) := by
  have h : (taylor_upper (H_rat 580 / 8) 15)^8 / 580 < (41/23 : ℚ) := by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]
  exact_mod_cast h

lemma taylor_le_exp (x : ℚ) (hx : 0 ≤ x) (n : ℕ) : (taylor_sum x n : ℝ) ≤ exp (x : ℝ) := by
  have := sum_le_exp_of_nonneg (x := (x : ℝ)) (by exact_mod_cast hx) n
  unfold taylor_sum
  push_cast
  exact this

lemma exp_le_taylor_upper (x : ℚ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (n : ℕ) (hn : 0 < n) :
    exp (x : ℝ) ≤ (taylor_upper x n : ℝ) := by
  have := exp_bound' (x := (x : ℝ)) (by exact_mod_cast h1) (by exact_mod_cast h2) hn
  unfold taylor_upper taylor_sum taylor_rem
  push_cast
  exact this

lemma taylor_pos (x : ℚ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ (taylor_sum x n : ℝ) := by
  unfold taylor_sum
  push_cast
  apply sum_nonneg
  intro i _
  positivity

lemma exp_H_300_lower : (16/9 : ℝ) < exp (H_rat 300) / 301 := by
  have h1 : (16/9 : ℝ) < ((taylor_sum (H_rat 300 / 8) 8)^8 / 301 : ℝ) := by
    have h := lower_bound_eval
    push_cast at h
    exact h
  have h2 : 0 ≤ H_rat 300 / 8 := by norm_num [H_rat]
  have h3 : (taylor_sum (H_rat 300 / 8) 8 : ℝ) ≤ exp ((H_rat 300 / 8 : ℚ) : ℝ) := taylor_le_exp _ h2 8
  have h4 : 0 ≤ (taylor_sum (H_rat 300 / 8) 8 : ℝ) := taylor_pos _ h2 8
  have h5 : (taylor_sum (H_rat 300 / 8) 8 : ℝ)^8 ≤ (exp ((H_rat 300 / 8 : ℚ) : ℝ))^8 := by
    gcongr
  have h6 : (exp ((H_rat 300 / 8 : ℚ) : ℝ))^8 = exp (H_rat 300 : ℝ) := by
    have : ((H_rat 300 / 8 : ℚ) : ℝ) = (H_rat 300 : ℝ) / 8 := by push_cast; rfl
    rw [this, ← exp_nat_mul]
    ring_nf
  linarith

lemma exp_H_580_upper : exp (H_rat 580) / 580 < (41/23 : ℝ) := by
  have h1 : (((taylor_upper (H_rat 580 / 8) 15)^8 / 580 : ℚ) : ℝ) < ((41/23 : ℚ) : ℝ) := upper_bound_eval
  have h1_r : (taylor_upper (H_rat 580 / 8) 15 : ℝ)^8 / 580 < (41/23 : ℝ) := by
    push_cast at h1
    exact h1
  have h2 : 0 ≤ H_rat 580 / 8 := by norm_num [H_rat]
  have h3 : H_rat 580 / 8 ≤ 1 := by norm_num [H_rat]
  have h4 : exp ((H_rat 580 / 8 : ℚ) : ℝ) ≤ (taylor_upper (H_rat 580 / 8) 15 : ℝ) := by
    apply exp_le_taylor_upper _ h2 h3 15 (by decide)
  have h5 : 0 ≤ exp ((H_rat 580 / 8 : ℚ) : ℝ) := exp_pos _ |>.le
  have h6 : (exp ((H_rat 580 / 8 : ℚ) : ℝ))^8 ≤ (taylor_upper (H_rat 580 / 8) 15 : ℝ)^8 := by
    gcongr
  have h7 : (exp ((H_rat 580 / 8 : ℚ) : ℝ))^8 = exp (H_rat 580 : ℝ) := by
    have : ((H_rat 580 / 8 : ℚ) : ℝ) = (H_rat 580 : ℝ) / 8 := by push_cast; rfl
    rw [this, ← exp_nat_mul]
    ring_nf
  linarith

lemma gamma_bounds : (16/9 : ℝ) < exp eulerMascheroniConstant ∧ exp eulerMascheroniConstant < (41/23 : ℝ) := by
  constructor
  · -- lower bound
    have h1 : eulerMascheroniSeq 300 < eulerMascheroniConstant :=
      eulerMascheroniSeq_lt_eulerMascheroniConstant 300
    have h2 : exp (eulerMascheroniSeq 300) < exp eulerMascheroniConstant :=
      exp_lt_exp.mpr h1
    have h3 : eulerMascheroniSeq 300 = (harmonic 300 : ℝ) - Real.log 301 := by
      unfold eulerMascheroniSeq
      have : ((300 : ℕ) + 1 : ℝ) = 301 := by norm_num
      rw [this]
    have h4 : exp ((harmonic 300 : ℝ) - Real.log 301) = exp (harmonic 300) / 301 := by
      rw [exp_sub, exp_log]
      · norm_num
    have h5 : (16/9 : ℝ) < exp (harmonic 300) / 301 := by
      have := exp_H_300_lower
      rw [H_rat_eq_harmonic] at this
      exact this
    rw [h3] at h2
    rw [h4] at h2
    linarith
  · -- upper bound
    have h1 : eulerMascheroniConstant < eulerMascheroniSeq' 580 :=
      eulerMascheroniConstant_lt_eulerMascheroniSeq' 580
    have h2 : exp eulerMascheroniConstant < exp (eulerMascheroniSeq' 580) :=
      exp_lt_exp.mpr h1
    have h3 : eulerMascheroniSeq' 580 = (harmonic 580 : ℝ) - Real.log 580 := rfl
    have h4 : exp ((harmonic 580 : ℝ) - Real.log 580) = exp (harmonic 580) / 580 := by
      rw [exp_sub, exp_log]
      · norm_num
    have h5 : exp (harmonic 580) / 580 < (41/23 : ℝ) := by
      have := exp_H_580_upper
      rw [H_rat_eq_harmonic] at this
      exact this
    rw [h3] at h2
    rw [h4] at h2
    linarith

lemma D_n_gt_1 (n : ℕ) (hn : 2 ≤ n) : 1 < exp (harmonic (n+1)) - exp (harmonic n) := by
  have h1 : (n : ℝ) * (16/9 : ℝ) < exp (harmonic n) := by
    have h_seq := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    have h_exp := exp_lt_exp.mpr h_seq
    have hn0 : n ≠ 0 := by omega
    have h_seq_eq : eulerMascheroniSeq' n = (harmonic n : ℝ) - Real.log n := by
      unfold eulerMascheroniSeq'
      simp [hn0]
    rw [h_seq_eq, exp_sub, exp_log] at h_exp
    · have h_gamma := gamma_bounds.1
      have h2 : (16/9 : ℝ) < exp (harmonic n) / n := by linarith
      have hp : 0 < (n : ℝ) := by exact Nat.cast_pos.mpr (by linarith)
      have h3 := (lt_div_iff₀ hp).mp h2
      calc
        (n : ℝ) * (16/9 : ℝ) = (16/9 : ℝ) * n := by ring
        _ < exp (harmonic n) := h3
    · exact Nat.cast_pos.mpr (by linarith)
  have h_diff : exp (harmonic (n+1)) - exp (harmonic n) = exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) := by
    have h_succ : (harmonic (n+1) : ℝ) = harmonic n + 1 / (n + 1 : ℝ) := by
      rw [harmonic_succ]
      push_cast
      rw [one_div]
    rw [h_succ, exp_add]
    ring
  have hx : 1 / (n + 1 : ℝ) ≤ exp (1 / (n + 1 : ℝ)) - 1 := by
    have := add_one_le_exp (1 / (n + 1 : ℝ))
    linarith
  have h_exp_pos : 0 < exp (harmonic n) := exp_pos _
  have h3 : exp (harmonic n) * (1 / (n + 1 : ℝ)) ≤ exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) := by
    gcongr
  have h4 : (n : ℝ) * (16/9 : ℝ) * (1 / (n + 1 : ℝ)) < exp (harmonic n) * (1 / (n + 1 : ℝ)) := by
    gcongr
  have h5 : 1 ≤ (n : ℝ) * (16/9 : ℝ) * (1 / (n + 1 : ℝ)) := by
    have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hp : 0 < 9 * ((n : ℝ) + 1) := by linarith
    have hp2 : (n + 1 : ℝ) ≠ 0 := by linarith
    have h_mul_eq : 9 * ((n : ℝ) + 1) * ((n : ℝ) * (16/9 : ℝ) * (1 / (n + 1 : ℝ))) = 16 * (n : ℝ) := by
      calc
        9 * ((n : ℝ) + 1) * ((n : ℝ) * (16/9 : ℝ) * (1 / (n + 1 : ℝ)))
          = (9 * (16/9 : ℝ)) * (n : ℝ) * (((n : ℝ) + 1) * (1 / (n + 1 : ℝ))) := by ring
        _ = 16 * (n : ℝ) * 1 := by
          congr 1
          · norm_num
          · rw [mul_one_div]
            exact div_self hp2
        _ = 16 * (n : ℝ) := by ring
    have h_mul_ineq : 9 * ((n : ℝ) + 1) * 1 ≤ 9 * ((n : ℝ) + 1) * ((n : ℝ) * (16/9 : ℝ) * (1 / (n + 1 : ℝ))) := by
      rw [h_mul_eq]
      linarith
    exact (mul_le_mul_iff_of_pos_left hp).mp h_mul_ineq
  linarith

lemma exp_minus_one_le_quad (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x ≤ 1) : exp x - 1 ≤ x + x^2 := by
  have h := exp_bound' hx1 hx2 (n := 2) (by norm_num)
  have h_sum : (range 2).sum (fun m => x^m / (Nat.factorial m : ℝ)) = 1 + x := by
    rw [sum_range_succ, sum_range_one]
    simp
  have h_rem : x^2 * ((2:ℕ) + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * (2:ℕ)) = x^2 * (3/4) := by
    norm_num
    ring
  have h_full : (range 2).sum (fun m => x^m / (Nat.factorial m : ℝ)) + x^2 * ((2:ℕ) + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * (2:ℕ)) = 1 + x + x^2 * (3/4) := by
    rw [h_sum, h_rem]
  rw [h_full] at h
  have : x^2 * (3/4) ≤ x^2 := by
    nlinarith
  linarith

lemma D_n_lt_2 (n : ℕ) (hn : 8 ≤ n) : exp (harmonic (n+1)) - exp (harmonic n) < 2 := by
  have h1 : exp (harmonic n) < (n + 1 : ℝ) * (41/23 : ℝ) := by
    have h_seq := eulerMascheroniSeq_lt_eulerMascheroniConstant n
    have h_exp := exp_lt_exp.mpr h_seq
    have h_seq_eq : eulerMascheroniSeq n = (harmonic n : ℝ) - Real.log (n + 1) := rfl
    rw [h_seq_eq, exp_sub, exp_log] at h_exp
    · have h_gamma := gamma_bounds.2
      have h2 : exp (harmonic n) / (n + 1 : ℝ) < (41/23 : ℝ) := by linarith
      have hp : 0 < (n + 1 : ℝ) := by positivity
      exact (div_lt_iff₀ hp).mp h2 |>.trans_le (by ring_nf; rfl)
    · positivity
  have h_diff : exp (harmonic (n+1)) - exp (harmonic n) = exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) := by
    have h_succ : (harmonic (n+1) : ℝ) = harmonic n + 1 / (n + 1 : ℝ) := by
      rw [harmonic_succ]
      push_cast
      rw [one_div]
    rw [h_succ, exp_add]
    ring
  have hx : 1 / (n + 1 : ℝ) ≤ 1 := by
    have : (9 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (by linarith : 9 ≤ n + 1)
    have : 1 / (n + 1 : ℝ) ≤ 1 / 9 := by apply one_div_le_one_div_of_le (by positivity) this
    linarith
  have hx_pos : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
  have h_quad := exp_minus_one_le_quad (1 / (n + 1 : ℝ)) hx_pos hx
  have h2 : exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) ≤ exp (harmonic n) * (1 / (n + 1 : ℝ) + (1 / (n + 1 : ℝ))^2) := by
    gcongr
  have h3 : exp (harmonic n) * (1 / (n + 1 : ℝ) + (1 / (n + 1 : ℝ))^2) < (n + 1 : ℝ) * (41/23 : ℝ) * (1 / (n + 1 : ℝ) + (1 / (n + 1 : ℝ))^2) := by
    gcongr
  have hp : (n + 1 : ℝ) ≠ 0 := by positivity
  have h4 : (n + 1 : ℝ) * (41/23 : ℝ) * (1 / (n + 1 : ℝ) + (1 / (n + 1 : ℝ))^2) < 2 := by
    calc
      (n + 1 : ℝ) * (41/23 : ℝ) * (1 / (n + 1 : ℝ) + (1 / (n + 1 : ℝ))^2)
        = (41/23 : ℝ) * (((n + 1 : ℝ) * (1 / (n + 1 : ℝ))) + (n + 1 : ℝ) * ((1 / (n + 1 : ℝ)) * (1 / (n + 1 : ℝ)))) := by ring
      _ = (41/23 : ℝ) * (1 + 1 / (n + 1 : ℝ)) := by
        congr 1
        have hp1 : (n + 1 : ℝ) * (1 / (n + 1 : ℝ)) = 1 := by
          rw [mul_one_div, div_self hp]
        rw [hp1]
        calc
          1 + (n + 1 : ℝ) * (1 / (n + 1 : ℝ) * (1 / (n + 1 : ℝ))) = 1 + ((n + 1 : ℝ) * (1 / (n + 1 : ℝ))) * (1 / (n + 1 : ℝ)) := by ring
          _ = 1 + 1 * (1 / (n + 1 : ℝ)) := by rw [hp1]
          _ = 1 + 1 / (n + 1 : ℝ) := by ring
      _ ≤ (41/23 : ℝ) * (1 + 1 / 9) := by
        have h_9_le : (9 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (by linarith : 9 ≤ n + 1)
        have h_9_pos : (0 : ℝ) < 9 := by norm_num
        have h_np1_pos : 0 < (n + 1 : ℝ) := by exact Nat.cast_add_one_pos n
        have h_div : 1 / (n + 1 : ℝ) ≤ 1 / 9 := (one_div_le_one_div h_np1_pos h_9_pos).mpr h_9_le
        linarith
      _ < 2 := by norm_num
  linarith

lemma D_n_bound_check (n : ℕ) (h_upper : (((taylor_upper (H_rat (n+1) / 4) 8)^4 : ℚ) : ℝ) - (((taylor_sum (H_rat n / 4) 8)^4 : ℚ) : ℝ) < 2)
    (h_le_np1 : H_rat (n+1) / 4 ≤ 1) :
    exp (harmonic (n+1)) - exp (harmonic n) < 2 := by
  have hr : (taylor_upper (H_rat (n+1) / 4) 8 : ℝ)^4 - (taylor_sum (H_rat n / 4) 8 : ℝ)^4 < 2 := by
    push_cast at h_upper
    exact h_upper
  have h_pos_n : 0 ≤ H_rat n / 4 := by
    unfold H_rat
    apply div_nonneg
    · apply sum_nonneg; intro i _; positivity
    · norm_num
  have h_pos_np1 : 0 ≤ H_rat (n+1) / 4 := by
    unfold H_rat
    apply div_nonneg
    · apply sum_nonneg; intro i _; positivity
    · norm_num
  have h1 : exp ((H_rat (n+1) / 4 : ℚ) : ℝ) ≤ (taylor_upper (H_rat (n+1) / 4) 8 : ℝ) := by
    apply exp_le_taylor_upper _ h_pos_np1 h_le_np1 8 (by decide)
  have h2 : (taylor_sum (H_rat n / 4) 8 : ℝ) ≤ exp ((H_rat n / 4 : ℚ) : ℝ) := by
    apply taylor_le_exp _ h_pos_n 8
  have h3 : 0 ≤ exp ((H_rat (n+1) / 4 : ℚ) : ℝ) := exp_pos _ |>.le
  have h4 : 0 ≤ (taylor_sum (H_rat n / 4) 8 : ℝ) := taylor_pos _ h_pos_n 8
  have h5 : (exp ((H_rat (n+1) / 4 : ℚ) : ℝ))^4 ≤ (taylor_upper (H_rat (n+1) / 4) 8 : ℝ)^4 := by
    gcongr
  have h6 : (taylor_sum (H_rat n / 4) 8 : ℝ)^4 ≤ (exp ((H_rat n / 4 : ℚ) : ℝ))^4 := by
    gcongr
  have h7 : (exp ((H_rat (n+1) / 4 : ℚ) : ℝ))^4 = exp (H_rat (n+1) : ℝ) := by
    have : ((H_rat (n+1) / 4 : ℚ) : ℝ) = (H_rat (n+1) : ℝ) / 4 := by push_cast; rfl
    rw [this, ← exp_nat_mul]
    ring_nf
  have h8 : (exp ((H_rat n / 4 : ℚ) : ℝ))^4 = exp (H_rat n : ℝ) := by
    have : ((H_rat n / 4 : ℚ) : ℝ) = (H_rat n : ℝ) / 4 := by push_cast; rfl
    rw [this, ← exp_nat_mul]
    ring_nf
  have h9 : exp (H_rat (n+1) : ℝ) - exp (H_rat n : ℝ) < 2 := by linarith
  rw [H_rat_eq_harmonic, H_rat_eq_harmonic] at h9
  exact h9

lemma D_1_lt_2 : exp (harmonic 2) - exp (harmonic 1) < 2 := D_n_bound_check 1 (by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]) (by norm_num [H_rat])
lemma D_2_lt_2 : exp (harmonic 3) - exp (harmonic 2) < 2 := D_n_bound_check 2 (by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]) (by norm_num [H_rat])
lemma D_3_lt_2 : exp (harmonic 4) - exp (harmonic 3) < 2 := D_n_bound_check 3 (by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]) (by norm_num [H_rat])
lemma D_4_lt_2 : exp (harmonic 5) - exp (harmonic 4) < 2 := D_n_bound_check 4 (by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]) (by norm_num [H_rat])
lemma D_5_lt_2 : exp (harmonic 6) - exp (harmonic 5) < 2 := D_n_bound_check 5 (by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]) (by norm_num [H_rat])
lemma D_6_lt_2 : exp (harmonic 7) - exp (harmonic 6) < 2 := D_n_bound_check 6 (by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]) (by norm_num [H_rat])
lemma D_7_lt_2 : exp (harmonic 8) - exp (harmonic 7) < 2 := D_n_bound_check 7 (by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]) (by norm_num [H_rat])

lemma D_n_lt_2_all (n : ℕ) (hn : 1 ≤ n) : exp (harmonic (n+1)) - exp (harmonic n) < 2 := by
  have h1 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n := by omega
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_8
  · exact D_1_lt_2
  · exact D_2_lt_2
  · exact D_3_lt_2
  · exact D_4_lt_2
  · exact D_5_lt_2
  · exact D_6_lt_2
  · exact D_7_lt_2
  · exact D_n_lt_2 n h_8


open Topology

lemma harmonic_nonneg (n : ℕ) : 0 ≤ harmonic n := by
  induction' n with n ih
  · simp
  · rw [harmonic_succ]
    positivity

lemma exp_harmonic_ge_1 (n : ℕ) : 1 ≤ exp (harmonic n) := by
  have : (1:ℝ) = exp 0 := by norm_num
  rw [this]
  apply exp_le_exp.mpr
  exact_mod_cast harmonic_nonneg n

lemma nat_floor_eq_int_floor (a : ℝ) (ha : 0 ≤ a) : (⌊a⌋₊ : ℤ) = ⌊a⌋ := by
  have h1 : (⌊a⌋₊ : ℝ) ≤ a ∧ a < (⌊a⌋₊ : ℝ) + 1 := by
    exact (Nat.floor_eq_iff ha).mp rfl
  have h2 : ((⌊a⌋₊ : ℤ) : ℝ) ≤ a ∧ a < ((⌊a⌋₊ : ℤ) : ℝ) + 1 := by
    push_cast
    exact h1
  exact (Int.floor_eq_iff.mpr h2).symm

lemma diff_eq_floor (n : ℕ) : A206911_diff n = 1 + ⌊exp (harmonic (n+1)) - 1⌋ - ⌊exp (harmonic n) - 1⌋ := by
  unfold A206911_diff A206911
  have h_H_np1 : (range (n+1)).sum (fun k => 1 / ((k : ℝ) + 1)) = harmonic (n+1) := by
    unfold harmonic
    push_cast
    apply sum_congr rfl
    intro x _
    rw [one_div]
  have h_H_n : (range n).sum (fun k => 1 / ((k : ℝ) + 1)) = harmonic n := by
    unfold harmonic
    push_cast
    apply sum_congr rfl
    intro x _
    rw [one_div]
  rw [h_H_np1, h_H_n]
  have hp1 : 0 ≤ exp (harmonic (n+1)) - 1 := by
    have := exp_harmonic_ge_1 (n+1)
    linarith
  have hp2 : 0 ≤ exp (harmonic n) - 1 := by
    have := exp_harmonic_ge_1 n
    linarith
  have h1 : ((⌊exp (harmonic (n+1)) - 1⌋₊ : ℤ).toNat : ℤ) = ⌊exp (harmonic (n+1)) - 1⌋ := by
    have h := Int.toNat_natCast ⌊exp (harmonic (n+1)) - 1⌋₊
    rw [h]
    exact nat_floor_eq_int_floor _ hp1
  have h2 : ((⌊exp (harmonic n) - 1⌋₊ : ℤ).toNat : ℤ) = ⌊exp (harmonic n) - 1⌋ := by
    have h := Int.toNat_natCast ⌊exp (harmonic n) - 1⌋₊
    rw [h]
    exact nat_floor_eq_int_floor _ hp2
  change ((n + 1 : ℕ) : ℤ) + ((⌊exp ↑(harmonic (n + 1)) - 1⌋₊ : ℤ).toNat : ℤ) - (((n : ℕ) : ℤ) + ((⌊exp ↑(harmonic n) - 1⌋₊ : ℤ).toNat : ℤ)) = 1 + ⌊exp ↑(harmonic (n + 1)) - 1⌋ - ⌊exp ↑(harmonic n) - 1⌋
  rw [h1, h2]
  push_cast
  ring


lemma D_n_val (x y : ℝ) (h1 : 1 < y - x) (h2 : y - x < 2) :
    1 + ⌊y⌋ - ⌊x⌋ = 2 ∨ 1 + ⌊y⌋ - ⌊x⌋ = 3 := by
  have h_high : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h_low : y - 1 < (⌊y⌋ : ℝ) := Int.sub_one_lt_floor y
  have h_high2 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h_low2 : x - 1 < (⌊x⌋ : ℝ) := Int.sub_one_lt_floor x
  have h_int_diff2 : 0 < ⌊y⌋ - ⌊x⌋ := by
    rw [← Int.cast_pos (R := ℝ)]
    push_cast
    linarith
  have h_int_diff3 : ⌊y⌋ - ⌊x⌋ < 3 := by
    rw [← Int.cast_lt (R := ℝ)]
    push_cast
    linarith
  omega

lemma D_n_gt_1_check (n : ℕ) (h_lower : 1 < (((taylor_sum (H_rat (n+1) / 4) 8)^4 : ℚ) : ℝ) - (((taylor_upper (H_rat n / 4) 8)^4 : ℚ) : ℝ))
    (h_le_n : H_rat n / 4 ≤ 1) :
    1 < exp (harmonic (n+1)) - exp (harmonic n) := by
  have hr : 1 < (taylor_sum (H_rat (n+1) / 4) 8 : ℝ)^4 - (taylor_upper (H_rat n / 4) 8 : ℝ)^4 := by
    push_cast at h_lower
    exact h_lower
  have h_pos_n : 0 ≤ H_rat n / 4 := by
    unfold H_rat
    apply div_nonneg
    · apply sum_nonneg; intro i _; positivity
    · norm_num
  have h_pos_np1 : 0 ≤ H_rat (n+1) / 4 := by
    unfold H_rat
    apply div_nonneg
    · apply sum_nonneg; intro i _; positivity
    · norm_num
  have h1 : exp ((H_rat n / 4 : ℚ) : ℝ) ≤ (taylor_upper (H_rat n / 4) 8 : ℝ) := by
    apply exp_le_taylor_upper _ h_pos_n h_le_n 8 (by decide)
  have h2 : (taylor_sum (H_rat (n+1) / 4) 8 : ℝ) ≤ exp ((H_rat (n+1) / 4 : ℚ) : ℝ) := by
    apply taylor_le_exp _ h_pos_np1 8
  have h3 : 0 ≤ exp ((H_rat n / 4 : ℚ) : ℝ) := exp_pos _ |>.le
  have h4 : 0 ≤ (taylor_sum (H_rat (n+1) / 4) 8 : ℝ) := taylor_pos _ h_pos_np1 8
  have h5 : (exp ((H_rat n / 4 : ℚ) : ℝ))^4 ≤ (taylor_upper (H_rat n / 4) 8 : ℝ)^4 := by
    gcongr
  have h6 : (taylor_sum (H_rat (n+1) / 4) 8 : ℝ)^4 ≤ (exp ((H_rat (n+1) / 4 : ℚ) : ℝ))^4 := by
    gcongr
  have h7 : (exp ((H_rat (n+1) / 4 : ℚ) : ℝ))^4 = exp (H_rat (n+1) : ℝ) := by
    have : ((H_rat (n+1) / 4 : ℚ) : ℝ) = (H_rat (n+1) : ℝ) / 4 := by push_cast; rfl
    rw [this, ← exp_nat_mul]
    ring_nf
  have h8 : (exp ((H_rat n / 4 : ℚ) : ℝ))^4 = exp (H_rat n : ℝ) := by
    have : ((H_rat n / 4 : ℚ) : ℝ) = (H_rat n : ℝ) / 4 := by push_cast; rfl
    rw [this, ← exp_nat_mul]
    ring_nf
  have h9 : 1 < exp (H_rat (n+1) : ℝ) - exp (H_rat n : ℝ) := by linarith
  rw [H_rat_eq_harmonic, H_rat_eq_harmonic] at h9
  exact h9

lemma D_1_gt_1 : 1 < exp (harmonic 2) - exp (harmonic 1) := D_n_gt_1_check 1 (by norm_num [taylor_upper, taylor_sum, taylor_rem, H_rat]) (by norm_num [H_rat])

lemma D_n_gt_1_all (n : ℕ) (hn : 1 ≤ n) : 1 < exp (harmonic (n+1)) - exp (harmonic n) := by
  have h1 : n = 1 ∨ 2 ≤ n := by omega
  rcases h1 with rfl | h_2
  · exact D_1_gt_1
  · exact D_n_gt_1 n h_2

lemma A206911_diff_in_set (n : ℕ) (hn : 1 ≤ n) : A206911_diff n ∈ ({2, 3} : Set ℤ) := by
  rw [diff_eq_floor]
  have h1 : 1 < exp (harmonic (n+1)) - exp (harmonic n) := D_n_gt_1_all _ hn
  have h2 : exp (harmonic (n+1)) - exp (harmonic n) < 2 := D_n_lt_2_all _ hn
  have h_diff := D_n_val (exp (harmonic n) - 1) (exp (harmonic (n+1)) - 1)
  have h_diff1 : 1 < exp (harmonic (n + 1)) - 1 - (exp (harmonic n) - 1) := by linarith
  have h_diff2 : exp (harmonic (n + 1)) - 1 - (exp (harmonic n) - 1) < 2 := by linarith
  have h3 := h_diff h_diff1 h_diff2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h3 with h | h
  · left; exact h
  · right; exact h


lemma A206911_diff_is_2_or_3 (n : ℕ) (hn : 1 ≤ n) : A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  have h := A206911_diff_in_set n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  exact h

lemma sum_A206911_diff (N : ℕ) :
    (range N).sum (fun n => A206911_diff (n + 1)) = ⌊exp (harmonic (N+1)) - 1⌋ - ⌊exp (harmonic 1) - 1⌋ + N := by
  have h : (range N).sum (fun n => A206911_diff (n + 1)) = (range N).sum (fun n => (1 : ℤ) + (⌊exp (harmonic (n+2)) - 1⌋ - ⌊exp (harmonic (n+1)) - 1⌋)) := by
    apply sum_congr rfl
    intro x _
    rw [diff_eq_floor]
    ring
  rw [h]
  have h2 : (range N).sum (fun n => (1 : ℤ) + (⌊exp (harmonic (n+2)) - 1⌋ - ⌊exp (harmonic (n+1)) - 1⌋)) = ((range N).sum (fun n => (1 : ℤ))) + (range N).sum (fun n => ⌊exp (harmonic (n+2)) - 1⌋ - ⌊exp (harmonic (n+1)) - 1⌋) := by
    exact sum_add_distrib
  rw [h2]
  have h3 : (range N).sum (fun n => (1 : ℤ)) = N := by simp
  have h4 : (range N).sum (fun n => ⌊exp (harmonic (n+2)) - 1⌋ - ⌊exp (harmonic (n+1)) - 1⌋) = ⌊exp (harmonic (N+1)) - 1⌋ - ⌊exp (harmonic 1) - 1⌋ := by
    exact sum_range_sub (fun n => ⌊exp (harmonic (n+1)) - 1⌋) N
  linarith
lemma count_threes_eq (N : ℕ) : (count_threes N : ℤ) = (range N).sum (fun n => A206911_diff (n + 1) - 2) := by
  unfold count_threes
  push_cast
  apply sum_congr rfl
  intro x _
  have h_val := A206911_diff_is_2_or_3 (x + 1) (by omega)
  rcases h_val with h | h
  · rw [h, if_neg (by decide)]
    norm_num
  · rw [h, if_pos rfl]
    norm_num

lemma count_threes_closed_form (N : ℕ) :
    (count_threes N : ℤ) = ⌊exp (harmonic (N+1)) - 1⌋ - ⌊exp (harmonic 1) - 1⌋ - N := by
  rw [count_threes_eq]
  have h1 : (range N).sum (fun n => A206911_diff (n + 1) - 2) = (range N).sum (fun n => A206911_diff (n + 1)) - (range N).sum (fun n => (2 : ℤ)) := by
    exact sum_sub_distrib (s := range N) (f := fun n => A206911_diff (n+1)) (g := fun n => (2:ℤ))
  rw [h1]
  rw [sum_A206911_diff]
  simp
  ring

lemma count_twos_closed_form (N : ℕ) :
    (count_twos N : ℤ) = 2 * N - ⌊exp (harmonic (N+1)) - 1⌋ + ⌊exp (harmonic 1) - 1⌋ := by
  unfold count_twos
  have h_le : count_threes N ≤ N := by
    unfold count_threes
    have h1 : (range N).sum (fun n => if A206911_diff (n + 1) = 3 then 1 else 0) ≤ (range N).sum (fun n => 1) := by
      apply sum_le_sum
      intro i _
      split
      · rfl
      · exact Nat.zero_le 1
    have h2 : (range N).sum (fun n => 1) = N := by simp
    rw [h2] at h1
    exact h1
  rw [Int.ofNat_sub h_le]
  rw [count_threes_closed_form]
  ring


open Real Nat Finset Filter

lemma exp_harmonic_div_tendsto :
    Tendsto (fun N : ℕ => exp (harmonic N) / ((N : ℝ) + 1)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h1 : Tendsto eulerMascheroniSeq atTop (nhds eulerMascheroniConstant) :=
    tendsto_eulerMascheroniSeq
  have h2 : Tendsto (fun N : ℕ => exp (eulerMascheroniSeq N)) atTop (nhds (exp eulerMascheroniConstant)) :=
    (continuous_exp.tendsto eulerMascheroniConstant).comp h1
  have h_eq : ∀ᶠ N in atTop, exp (eulerMascheroniSeq N) = exp (harmonic N) / ((N : ℝ) + 1) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    unfold eulerMascheroniSeq
    rw [exp_sub, exp_log]
    positivity
  exact (tendsto_congr' h_eq).mp h2

lemma exp_harmonic_div_N_tendsto :
    Tendsto (fun N : ℕ => exp (harmonic (N+1)) / (N : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h1 : Tendsto (fun N : ℕ => exp (harmonic (N+1)) / ((N : ℝ) + 2)) atTop (nhds (exp eulerMascheroniConstant)) := by
    have h_shift := Tendsto.comp exp_harmonic_div_tendsto (tendsto_add_atTop_nat 1)
    have h_eq : ∀ᶠ N in atTop, (fun N : ℕ => exp (harmonic N) / ((N : ℝ) + 1)) (N + 1) = exp (harmonic (N+1)) / ((N : ℝ) + 2) := by
      filter_upwards [] with N
      push_cast
      ring_nf
    exact (tendsto_congr' h_eq).mp h_shift
  
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ) + 2) / (N : ℝ)) atTop (nhds 1) := by
    have h_eq : ∀ᶠ (N : ℕ) in atTop, ((N : ℝ) + 2) / (N : ℝ) = 1 + 2 * (1 / (N : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [add_div]
      have : (N:ℝ) / (N:ℝ) = 1 := div_self (by positivity)
      rw [this]
      ring
    have h_lim := Tendsto.add (tendsto_const_nhds (x := (1:ℝ))) (Tendsto.const_mul (2:ℝ) (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have h_lim2 : Tendsto (fun N : ℕ => 1 + 2 * (1 / (N : ℝ))) atTop (nhds (1 + 2 * 0)) := h_lim
    have h_lim3 : Tendsto (fun N : ℕ => 1 + 2 * (1 / (N : ℝ))) atTop (nhds 1) := by
      simpa using h_lim2
    exact (tendsto_congr' h_eq).mpr h_lim3
  
  have h_prod := Tendsto.mul h1 h2
  have h_eq : ∀ᶠ (N : ℕ) in atTop, (exp (harmonic (N+1)) / ((N : ℝ) + 2)) * (((N : ℝ) + 2) / (N : ℝ)) = exp (harmonic (N+1)) / (N : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hp : ((N : ℝ) + 2) ≠ 0 := by positivity
    calc
      (exp (harmonic (N+1)) / ((N : ℝ) + 2)) * (((N : ℝ) + 2) / (N : ℝ))
        = (exp (harmonic (N+1)) / (N : ℝ)) * (((N : ℝ) + 2) / ((N : ℝ) + 2)) := by ring
      _ = (exp (harmonic (N+1)) / (N : ℝ)) * 1 := by rw [div_self hp]
      _ = exp (harmonic (N+1)) / (N : ℝ) := by ring
  have h_lim4 : Tendsto (fun N : ℕ => exp (harmonic (N+1)) / (N : ℝ)) atTop (nhds (exp eulerMascheroniConstant * 1)) :=
    (tendsto_congr' h_eq).mp h_prod
  simpa using h_lim4

lemma floor_exp_div_N_tendsto :
    Tendsto (fun N : ℕ => (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) / (N : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h_upper : ∀ᶠ N : ℕ in atTop, (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) / (N : ℝ) ≤ exp (harmonic (N+1)) / (N : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 : (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) ≤ exp (harmonic (N+1)) - 1 := Int.floor_le _
    have h2 : exp (harmonic (N+1)) - 1 ≤ exp (harmonic (N+1)) := by linarith
    have h3 : (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) ≤ exp (harmonic (N+1)) := h1.trans h2
    exact div_le_div_of_nonneg_right h3 (by exact Nat.cast_pos.mpr hN |>.le)

  have h_lower : ∀ᶠ N : ℕ in atTop, (exp (harmonic (N+1)) - 2) / (N : ℝ) ≤ (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) / (N : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 : exp (harmonic (N+1)) - 1 - 1 < (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) := Int.sub_one_lt_floor _
    have h2 : exp (harmonic (N+1)) - 2 ≤ (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) := by linarith
    exact div_le_div_of_nonneg_right h2 (by exact Nat.cast_pos.mpr hN |>.le)

  have h_lim_upper : Tendsto (fun N : ℕ => exp (harmonic (N+1)) / (N : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) :=
    exp_harmonic_div_N_tendsto

  have h_lim_lower : Tendsto (fun N : ℕ => (exp (harmonic (N+1)) - 2) / (N : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
    have h_eq : ∀ᶠ N : ℕ in atTop, (exp (harmonic (N+1)) - 2) / (N : ℝ) = exp (harmonic (N+1)) / (N : ℝ) - 2 * (1 / (N : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      calc
        (exp (harmonic (N+1)) - 2) / (N : ℝ) = exp (harmonic (N+1)) / (N : ℝ) - 2 / (N : ℝ) := by ring
        _ = exp (harmonic (N+1)) / (N : ℝ) - 2 * (1 / (N : ℝ)) := by ring
    have h_lim := Tendsto.sub exp_harmonic_div_N_tendsto (Tendsto.const_mul 2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have h_lim2 : Tendsto (fun N : ℕ => exp (harmonic (N+1)) / (N : ℝ) - 2 * (1 / (N : ℝ))) atTop (nhds (exp eulerMascheroniConstant - 2 * 0)) := h_lim
    have h_lim3 : Tendsto (fun N : ℕ => exp (harmonic (N+1)) / (N : ℝ) - 2 * (1 / (N : ℝ))) atTop (nhds (exp eulerMascheroniConstant)) := by
      simpa using h_lim2
    exact (tendsto_congr' h_eq).mpr h_lim3

  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lim_lower h_lim_upper h_lower h_upper

lemma count_threes_div_N_tendsto :
    Tendsto (fun N : ℕ => (count_threes N : ℝ) / (N : ℝ)) atTop (nhds (exp eulerMascheroniConstant - 1)) := by
  have h_eq : ∀ᶠ N : ℕ in atTop, (count_threes N : ℝ) / (N : ℝ) = (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) / (N : ℝ) - (⌊exp (harmonic 1) - 1⌋ : ℝ) / (N : ℝ) - 1 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hc := count_threes_closed_form N
    have hc_real : (count_threes N : ℝ) = (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) - (⌊exp (harmonic 1) - 1⌋ : ℝ) - (N : ℝ) := by exact_mod_cast hc
    rw [hc_real]
    have hn_pos : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    calc
      ((⌊exp (harmonic (N+1)) - 1⌋ : ℝ) - (⌊exp (harmonic 1) - 1⌋ : ℝ) - (N : ℝ)) / (N : ℝ)
        = (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) / (N : ℝ) - (⌊exp (harmonic 1) - 1⌋ : ℝ) / (N : ℝ) - (N : ℝ) / (N : ℝ) := by ring
      _ = (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) / (N : ℝ) - (⌊exp (harmonic 1) - 1⌋ : ℝ) / (N : ℝ) - 1 := by rw [div_self hn_pos]
  have h_lim1 := floor_exp_div_N_tendsto
  have h_lim2 : Tendsto (fun N : ℕ => (⌊exp (harmonic 1) - 1⌋ : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    have h_lim := Tendsto.const_mul (⌊exp (harmonic 1) - 1⌋ : ℝ) (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h_eq2 : ∀ᶠ N : ℕ in atTop, (⌊exp (harmonic 1) - 1⌋ : ℝ) / (N : ℝ) = (⌊exp (harmonic 1) - 1⌋ : ℝ) * (1 / (N : ℝ)) := by
      filter_upwards [] with N
      ring
    have h_lim_zero : Tendsto (fun N : ℕ => (⌊exp (harmonic 1) - 1⌋ : ℝ) * (1 / (N : ℝ))) atTop (nhds 0) := by
      simpa using h_lim
    exact (tendsto_congr' h_eq2).mpr h_lim_zero
  have h_lim3 := Tendsto.sub (Tendsto.sub h_lim1 h_lim2) (tendsto_const_nhds (x := (1:ℝ)))
  have h_lim4 : Tendsto (fun N : ℕ => (⌊exp (harmonic (N+1)) - 1⌋ : ℝ) / (N : ℝ) - (⌊exp (harmonic 1) - 1⌋ : ℝ) / (N : ℝ) - 1) atTop (nhds (exp eulerMascheroniConstant - 1)) := by
    have h_sub : exp eulerMascheroniConstant - 0 - 1 = exp eulerMascheroniConstant - 1 := by ring
    rw [← h_sub]
    exact h_lim3
  exact (tendsto_congr' h_eq).mpr h_lim4

lemma count_twos_div_N_tendsto :
    Tendsto (fun N : ℕ => (count_twos N : ℝ) / (N : ℝ)) atTop (nhds (2 - exp eulerMascheroniConstant)) := by
  have h_eq : ∀ᶠ N : ℕ in atTop, (count_twos N : ℝ) / (N : ℝ) = 1 - (count_threes N : ℝ) / (N : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    unfold count_twos
    have h_le : count_threes N ≤ N := by
      unfold count_threes
      have h1 : (range N).sum (fun n => if A206911_diff (n + 1) = 3 then 1 else 0) ≤ (range N).sum (fun n => 1) := by
        apply sum_le_sum
        intro i _
        split
        · rfl
        · exact Nat.zero_le 1
      have h2 : (range N).sum (fun n => 1) = N := by simp
      rw [h2] at h1
      exact h1
    have h_sub : ((N - count_threes N : ℕ) : ℝ) = (N : ℝ) - (count_threes N : ℝ) := by
      exact Nat.cast_sub h_le
    have hn_pos : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    calc
      (((N - count_threes N : ℕ) : ℝ)) / (N : ℝ)
        = ((N : ℝ) - (count_threes N : ℝ)) / (N : ℝ) := by rw [h_sub]
      _
        = (N : ℝ) / (N : ℝ) - (count_threes N : ℝ) / (N : ℝ) := sub_div _ _ _
      _ = 1 - (count_threes N : ℝ) / (N : ℝ) := by rw [div_self hn_pos]
  have h_lim := Tendsto.sub (tendsto_const_nhds (x := (1:ℝ))) count_threes_div_N_tendsto
  have h_lim2 : Tendsto (fun N : ℕ => 1 - (count_threes N : ℝ) / (N : ℝ)) atTop (nhds (2 - exp eulerMascheroniConstant)) := by
    have h_sub : 1 - (exp eulerMascheroniConstant - 1) = 2 - exp eulerMascheroniConstant := by ring
    rw [← h_sub]
    exact h_lim
  exact (tendsto_congr' h_eq).mpr h_lim2

lemma ratio_tendsto :
    Tendsto ratio_threes_to_twos atTop (nhds ((exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant))) := by
  have h_lim1 := count_threes_div_N_tendsto
  have h_lim2 := count_twos_div_N_tendsto
  have h_denom : 2 - exp eulerMascheroniConstant ≠ 0 := by
    have h1 : (16/9 : ℝ) < exp eulerMascheroniConstant := gamma_bounds.1
    have h2 : exp eulerMascheroniConstant < (41/23 : ℝ) := gamma_bounds.2
    linarith
  have h_lim := Tendsto.div h_lim1 h_lim2 h_denom
  have h_eq : ∀ᶠ N : ℕ in atTop, ratio_threes_to_twos N = ((count_threes N : ℝ) / (N : ℝ)) / ((count_twos N : ℝ) / (N : ℝ)) := by
    have h_denom_gt : 0 < 2 - exp eulerMascheroniConstant := by
      have h2 : exp eulerMascheroniConstant < (41/23 : ℝ) := gamma_bounds.2
      linarith
    have h_mem : Set.Ioi (0:ℝ) ∈ nhds (2 - exp eulerMascheroniConstant) := IsOpen.mem_nhds isOpen_Ioi h_denom_gt
    have h_eventually_pos : ∀ᶠ N in atTop, (count_twos N : ℝ) / (N : ℝ) > 0 := h_lim2 h_mem
    filter_upwards [h_eventually_pos, eventually_gt_atTop 0] with N hN2 hN
    unfold ratio_threes_to_twos
    have hc2 : (count_twos N : ℝ) / (N : ℝ) > 0 := hN2
    have hc2_ne_zero : count_twos N ≠ 0 := by
      intro h
      rw [h] at hc2
      push_cast at hc2
      have : (0 : ℝ) / (N : ℝ) = 0 := by exact zero_div (N : ℝ)
      rw [this] at hc2
      linarith
    rw [if_neg hc2_ne_zero]
    have hn_pos : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [div_div_div_cancel_right₀ hn_pos _ _]
  exact (tendsto_congr' h_eq).mpr h_lim


theorem oeis_a206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n ∈ ({2, 3} : Set ℤ)) ∧
  (∃ l : ℝ,
    3.5 < l ∧ l < 3.6 ∧
    Tendsto ratio_threes_to_twos atTop (nhds l)) := by
  constructor
  · exact A206911_diff_in_set
  · use (exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant)
    constructor
    · have h1 : (16/9 : ℝ) < exp eulerMascheroniConstant := gamma_bounds.1
      have h2 : exp eulerMascheroniConstant < (41/23 : ℝ) := gamma_bounds.2
      have h3 : 0 < 2 - exp eulerMascheroniConstant := by linarith
      have h4 : 3.5 * (2 - exp eulerMascheroniConstant) < exp eulerMascheroniConstant - 1 := by linarith
      exact (lt_div_iff₀ h3).mpr h4
    · constructor
      · have h1 : (16/9 : ℝ) < exp eulerMascheroniConstant := gamma_bounds.1
        have h2 : exp eulerMascheroniConstant < (41/23 : ℝ) := gamma_bounds.2
        have h3 : 0 < 2 - exp eulerMascheroniConstant := by linarith
        have h4 : exp eulerMascheroniConstant - 1 < 3.6 * (2 - exp eulerMascheroniConstant) := by linarith
        exact (div_lt_iff₀ h3).mpr h4
      · exact ratio_tendsto

theorem oeis_a206911_conjecture.disproof : ¬ (type_of% @oeis_a206911_conjecture) := by
  sorry
