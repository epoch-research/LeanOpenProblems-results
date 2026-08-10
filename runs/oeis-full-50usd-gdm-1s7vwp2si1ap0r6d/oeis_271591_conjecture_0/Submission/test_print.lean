import Mathlib

open Nat

def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  if h : T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

def is_maximal_run (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  (∀ i : ℕ, i < L → a (n + i) = v) ∧
  (a (n + L) ≠ v) ∧
  (a (n - 1) ≠ v)

instance (v n L : ℕ) : Decidable (is_maximal_run v n L) := by
  unfold is_maximal_run
  infer_instance

theorem check_0_run_small (n L : ℕ) (hn : n ≥ 2) (hn25 : n < 25) (h : is_maximal_run 0 n L) : L = 4 ∨ L = 5 := by
  revert L h
  interval_cases n <;> intro L h <;> decide

theorem check_1_run_small (n L : ℕ) (hn : n ≥ 2) (hn25 : n < 25) (h : is_maximal_run 1 n L) : L = 3 ∨ L = 4 := by
  revert L h
  interval_cases n <;> intro L h <;> decide



lemma testBit_iff_odd (m n : ℕ) : m.testBit n = true ↔ (m / 2^n) % 2 = 1 := by
  simp only [testBit, shiftRight_eq_div_pow, one_and_eq_mod_two]
  have h_or : (m / 2 ^ n) % 2 = 0 ∨ (m / 2 ^ n) % 2 = 1 := by
    have h_mod : (m / 2 ^ n) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  rcases h_or with h | h
  · rw [h]
    decide
  · rw [h]
    decide

lemma div_mod_omega (T X : ℕ) (hX : X > 0) (hT1 : 2 * X ≤ T) (hT2 : T < 4 * X) :
  (T / X) % 2 = 1 ↔ 3 * X ≤ T := by
  have h_le2 : 2 ≤ T / X := by
    rw [Nat.le_div_iff_mul_le hX]
    exact hT1
  have hT2' : T < X * 4 := by
    rw [Nat.mul_comm]
    exact hT2
  have h_lt4 : T / X < 4 := Nat.div_lt_of_lt_mul hT2'
  have h_le3 : 3 * X ≤ T ↔ 3 ≤ T / X := by
    rw [Nat.le_div_iff_mul_le hX]
  rw [h_le3]
  revert h_le2 h_lt4
  generalize T / X = Q
  intro h_le2 h_lt4
  omega

lemma testBit_K_iff (T K : ℕ) (h_bounds : 2^(K+1) ≤ T ∧ T < 2^(K+2)) :
  T.testBit K = true ↔ 3 * 2^K ≤ T := by
  have h_pow_gt : 2^K > 0 := Nat.pow_pos (by decide)
  have hT1 : 2 * 2^K ≤ T := by
    have h_pow : 2^(K+1) = 2 * 2^K := by ring
    omega
  have hT2 : T < 4 * 2^K := by
    have h_pow : 2^(K+2) = 4 * 2^K := by ring
    omega
  rw [testBit_iff_odd]
  exact div_mod_omega T (2^K) h_pow_gt hT1 hT2

lemma a_eq_cases (n K : ℕ) (h_bounds : 2^(K+1) ≤ tribonacci n ∧ tribonacci n < 2^(K+2)) (h_log : (tribonacci n).log2 - 1 = K) :
  (a n = 0 ↔ tribonacci n < 3 * 2^K) ∧ (a n = 1 ↔ 3 * 2^K ≤ tribonacci n) := by
  have h_pow : 2 ≤ 2^(K+1) := by
    have : 2^1 ≤ 2^(K+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact this
  have hT_gt : tribonacci n > 1 := by omega
  have h_not : ¬(tribonacci n ≤ 1) := by omega
  unfold a
  rw [dif_neg h_not]
  rw [h_log]
  dsimp only
  have h_test := testBit_K_iff (tribonacci n) K h_bounds
  cases h_bit : (tribonacci n).testBit K
  · have h_ineq : ¬(3 * 2^K ≤ tribonacci n) := by
      intro hc
      have h_t := h_test.mpr hc
      rw [h_bit] at h_t
      contradiction
    constructor
    · simp
      omega
    · simp
      omega
  · have h_ineq := h_test.mp h_bit
    constructor
    · simp
      omega
    · simp
      omega


lemma pow_rewrite_0 (K : ℕ) : 2^(K + 0) = 1 * 2^K := by ring
lemma pow_rewrite_1 (K : ℕ) : 2^(K + 1) = 2 * 2^K := by ring
lemma pow_rewrite_2 (K : ℕ) : 2^(K + 1 + 1) = 4 * 2^K := by ring
lemma pow_rewrite_3 (K : ℕ) : 2^(K + 1 + 1 + 1) = 8 * 2^K := by ring
lemma pow_rewrite_4 (K : ℕ) : 2^(K + 1 + 1 + 1 + 1) = 16 * 2^K := by ring
lemma pow_rewrite_5 (K : ℕ) : 2^(K + 1 + 1 + 1 + 1 + 1) = 32 * 2^K := by ring
lemma pow_rewrite_6 (K : ℕ) : 2^(K + 1 + 1 + 1 + 1 + 1 + 1) = 64 * 2^K := by ring
lemma pow_rewrite_7 (K : ℕ) : 2^(K + 1 + 1 + 1 + 1 + 1 + 1 + 1) = 128 * 2^K := by ring

lemma no_zero_run_of_length_6_generalized (T0 T1 T2 T3 T4 T5 : ℕ) (K0 K1 K2 K3 K4 K5 : ℕ)
  (h_rec1 : T3 = T2 + T1 + T0)
  (h_rec2 : T4 = T3 + T2 + T1)
  (h_rec3 : T5 = T4 + T3 + T2)
  (hK0 : 2^(K0+1) ≤ T0 ∧ T0 < 2^(K0+2))
  (hK1 : 2^(K1+1) ≤ T1 ∧ T1 < 2^(K1+2))
  (hK2 : 2^(K2+1) ≤ T2 ∧ T2 < 2^(K2+2))
  (hK3 : 2^(K3+1) ≤ T3 ∧ T3 < 2^(K3+2))
  (hK4 : 2^(K4+1) ≤ T4 ∧ T4 < 2^(K4+2))
  (hK5 : 2^(K5+1) ≤ T5 ∧ T5 < 2^(K5+2))
  (h_step1 : K1 = K0 ∨ K1 = K0 + 1)
  (h_step2 : K2 = K1 ∨ K2 = K1 + 1)
  (h_step3 : K3 = K2 ∨ K3 = K2 + 1)
  (h_step4 : K4 = K3 ∨ K4 = K3 + 1)
  (h_step5 : K5 = K4 ∨ K5 = K4 + 1)
  (hr0 : 183 * T0 ≤ 100 * T1 ∧ 500 * T1 ≤ 923 * T0)
  (hr1 : 183 * T1 ≤ 100 * T2 ∧ 500 * T2 ≤ 923 * T1)
  (hr2 : 183 * T2 ≤ 100 * T3 ∧ 500 * T3 ≤ 923 * T2)
  (hr3 : 183 * T3 ≤ 100 * T4 ∧ 500 * T4 ≤ 923 * T3)
  (hr4 : 183 * T4 ≤ 100 * T5 ∧ 500 * T5 ≤ 923 * T4)
  (ha0 : T0 < 3 * 2^K0)
  (ha1 : T1 < 3 * 2^K1)
  (ha2 : T2 < 3 * 2^K2)
  (ha3 : T3 < 3 * 2^K3)
  (ha4 : T4 < 3 * 2^K4)
  (ha5 : T5 < 3 * 2^K5) :
  False := by
  rcases h_step1 with h1 | h1 <;> subst h1 <;>
  rcases h_step2 with h2 | h2 <;> subst h2 <;>
  rcases h_step3 with h3 | h3 <;> subst h3 <;>
  rcases h_step4 with h4 | h4 <;> subst h4 <;>
  rcases h_step5 with h5 | h5 <;> subst h5
  all_goals
    simp only [pow_rewrite_1, pow_rewrite_2, pow_rewrite_3, pow_rewrite_4, pow_rewrite_5, pow_rewrite_6, pow_rewrite_7] at *
    try generalize 2^K0 = X at *
    try generalize 2^K1 = X at *
    try generalize 2^K2 = X at *
    try generalize 2^K3 = X at *
    try generalize 2^K4 = X at *
    try generalize 2^K5 = X at *
    omega






lemma no_0_run_length_1_generalized (T0 T1 T2 : ℕ) (K0 K1 K2 : ℕ)
  (hK0 : 2^(K0+1) ≤ T0 ∧ T0 < 2^(K0+2))
  (hK1 : 2^(K1+1) ≤ T1 ∧ T1 < 2^(K1+2))
  (hK2 : 2^(K2+1) ≤ T2 ∧ T2 < 2^(K2+2))
  (h_step1 : K1 = K0 ∨ K1 = K0 + 1)
  (h_step2 : K2 = K1 ∨ K2 = K1 + 1)
  (hr0 : 183 * T0 ≤ 100 * T1 ∧ 500 * T1 ≤ 923 * T0)
  (hr1 : 183 * T1 ≤ 100 * T2 ∧ 500 * T2 ≤ 923 * T1)
  (ha0 : 3 * 2^K0 ≤ T0)
  (ha1 : T1 < 3 * 2^K1)
  (ha2 : 3 * 2^K2 ≤ T2) :
  False := by
  rcases h_step1 with h1 | h1 <;> subst h1 <;>
  rcases h_step2 with h2 | h2 <;> subst h2
  all_goals
    simp only [pow_rewrite_1, pow_rewrite_2, pow_rewrite_3, pow_rewrite_4, pow_rewrite_5, pow_rewrite_6, pow_rewrite_7] at *
    try generalize 2^K0 = X at *
    try generalize 2^K1 = X at *
    try generalize 2^K2 = X at *
    omega


lemma no_0_run_length_2_generalized (T0 T1 T2 T3 : ℕ) (K0 K1 K2 K3 : ℕ)
  (hK0 : 2^(K0+1) ≤ T0 ∧ T0 < 2^(K0+2))
  (hK1 : 2^(K1+1) ≤ T1 ∧ T1 < 2^(K1+2))
  (hK2 : 2^(K2+1) ≤ T2 ∧ T2 < 2^(K2+2))
  (hK3 : 2^(K3+1) ≤ T3 ∧ T3 < 2^(K3+2))
  (h_step1 : K1 = K0 ∨ K1 = K0 + 1)
  (h_step2 : K2 = K1 ∨ K2 = K1 + 1)
  (h_step3 : K3 = K2 ∨ K3 = K2 + 1)
  (hr0 : 183 * T0 ≤ 100 * T1 ∧ 500 * T1 ≤ 923 * T0)
  (hr1 : 183 * T1 ≤ 100 * T2 ∧ 500 * T2 ≤ 923 * T1)
  (hr2 : 183 * T2 ≤ 100 * T3 ∧ 500 * T3 ≤ 923 * T2)
  (ha0 : 3 * 2^K0 ≤ T0)
  (ha1 : T1 < 3 * 2^K1)
  (ha2 : T2 < 3 * 2^K2)
  (ha3 : 3 * 2^K3 ≤ T3) :
  False := by
  rcases h_step1 with h1 | h1 <;> subst h1 <;>
  rcases h_step2 with h2 | h2 <;> subst h2 <;>
  rcases h_step3 with h3 | h3 <;> subst h3
  all_goals
    simp only [pow_rewrite_1, pow_rewrite_2, pow_rewrite_3, pow_rewrite_4, pow_rewrite_5, pow_rewrite_6, pow_rewrite_7] at *
    try generalize 2^K0 = X at *
    try generalize 2^K1 = X at *
    try generalize 2^K2 = X at *
    try generalize 2^K3 = X at *
    omega

lemma no_0_run_length_3_generalized (T0 T1 T2 T3 T4 : ℕ) (K0 K1 K2 K3 K4 : ℕ)
  (hK0 : 2^(K0+1) ≤ T0 ∧ T0 < 2^(K0+2))
  (hK1 : 2^(K1+1) ≤ T1 ∧ T1 < 2^(K1+2))
  (hK2 : 2^(K2+1) ≤ T2 ∧ T2 < 2^(K2+2))
  (hK3 : 2^(K3+1) ≤ T3 ∧ T3 < 2^(K3+2))
  (hK4 : 2^(K4+1) ≤ T4 ∧ T4 < 2^(K4+2))
  (h_step1 : K1 = K0 ∨ K1 = K0 + 1)
  (h_step2 : K2 = K1 ∨ K2 = K1 + 1)
  (h_step3 : K3 = K2 ∨ K3 = K2 + 1)
  (h_step4 : K4 = K3 ∨ K4 = K3 + 1)
  (hr0 : 183 * T0 ≤ 100 * T1 ∧ 500 * T1 ≤ 923 * T0)
  (hr1 : 183 * T1 ≤ 100 * T2 ∧ 500 * T2 ≤ 923 * T1)
  (hr2 : 183 * T2 ≤ 100 * T3 ∧ 500 * T3 ≤ 923 * T2)
  (hr3 : 183 * T3 ≤ 100 * T4 ∧ 500 * T4 ≤ 923 * T3)
  (ha0 : 3 * 2^K0 ≤ T0)
  (ha1 : T1 < 3 * 2^K1)
  (ha2 : T2 < 3 * 2^K2)
  (ha3 : T3 < 3 * 2^K3)
  (ha4 : 3 * 2^K4 ≤ T4) :
  False := by
  rcases h_step1 with h1 | h1 <;> subst h1 <;>
  rcases h_step2 with h2 | h2 <;> subst h2 <;>
  rcases h_step3 with h3 | h3 <;> subst h3 <;>
  rcases h_step4 with h4 | h4 <;> subst h4
  all_goals
    simp only [pow_rewrite_1, pow_rewrite_2, pow_rewrite_3, pow_rewrite_4, pow_rewrite_5, pow_rewrite_6, pow_rewrite_7] at *
    try generalize 2^K0 = X at *
    try generalize 2^K1 = X at *
    try generalize 2^K2 = X at *
    try generalize 2^K3 = X at *
    try generalize 2^K4 = X at *
    omega

lemma no_1_run_length_1_generalized (T0 T1 T2 : ℕ) (K0 K1 K2 : ℕ)
  (hK0 : 2^(K0+1) ≤ T0 ∧ T0 < 2^(K0+2))
  (hK1 : 2^(K1+1) ≤ T1 ∧ T1 < 2^(K1+2))
  (hK2 : 2^(K2+1) ≤ T2 ∧ T2 < 2^(K2+2))
  (h_step1 : K1 = K0 ∨ K1 = K0 + 1)
  (h_step2 : K2 = K1 ∨ K2 = K1 + 1)
  (hr0 : 183 * T0 ≤ 100 * T1 ∧ 500 * T1 ≤ 923 * T0)
  (hr1 : 183 * T1 ≤ 100 * T2 ∧ 500 * T2 ≤ 923 * T1)
  (ha0 : T0 < 3 * 2^K0)
  (ha1 : 3 * 2^K1 ≤ T1)
  (ha2 : T2 < 3 * 2^K2) :
  False := by
  rcases h_step1 with h1 | h1 <;> subst h1 <;>
  rcases h_step2 with h2 | h2 <;> subst h2
  all_goals
    simp only [pow_rewrite_1, pow_rewrite_2, pow_rewrite_3, pow_rewrite_4, pow_rewrite_5, pow_rewrite_6, pow_rewrite_7] at *
    try generalize 2^K0 = X at *
    try generalize 2^K1 = X at *
    try generalize 2^K2 = X at *
    omega

lemma no_1_run_length_2_generalized (T0 T1 T2 T3 : ℕ) (K0 K1 K2 K3 : ℕ)
  (hK0 : 2^(K0+1) ≤ T0 ∧ T0 < 2^(K0+2))
  (hK1 : 2^(K1+1) ≤ T1 ∧ T1 < 2^(K1+2))
  (hK2 : 2^(K2+1) ≤ T2 ∧ T2 < 2^(K2+2))
  (hK3 : 2^(K3+1) ≤ T3 ∧ T3 < 2^(K3+2))
  (h_step1 : K1 = K0 ∨ K1 = K0 + 1)
  (h_step2 : K2 = K1 ∨ K2 = K1 + 1)
  (h_step3 : K3 = K2 ∨ K3 = K2 + 1)
  (hr0 : 183 * T0 ≤ 100 * T1 ∧ 500 * T1 ≤ 923 * T0)
  (hr1 : 183 * T1 ≤ 100 * T2 ∧ 500 * T2 ≤ 923 * T1)
  (hr2 : 183 * T2 ≤ 100 * T3 ∧ 500 * T3 ≤ 923 * T2)
  (ha0 : T0 < 3 * 2^K0)
  (ha1 : 3 * 2^K1 ≤ T1)
  (ha2 : 3 * 2^K2 ≤ T2)
  (ha3 : T3 < 3 * 2^K3) :
  False := by
  rcases h_step1 with h1 | h1 <;> subst h1 <;>
  rcases h_step2 with h2 | h2 <;> subst h2 <;>
  rcases h_step3 with h3 | h3 <;> subst h3
  all_goals
    simp only [pow_rewrite_1, pow_rewrite_2, pow_rewrite_3, pow_rewrite_4, pow_rewrite_5, pow_rewrite_6, pow_rewrite_7] at *
    try generalize 2^K0 = X at *
    try generalize 2^K1 = X at *
    try generalize 2^K2 = X at *
    try generalize 2^K3 = X at *
    omega


lemma no_one_run_of_length_5_generalized (T0 T1 T2 T3 T4 : ℕ) (K0 K1 K2 K3 K4 : ℕ)
  (h_rec1 : T3 = T2 + T1 + T0)
  (h_rec2 : T4 = T3 + T2 + T1)
  (hK0 : 2^(K0+1) ≤ T0 ∧ T0 < 2^(K0+2))
  (hK1 : 2^(K1+1) ≤ T1 ∧ T1 < 2^(K1+2))
  (hK2 : 2^(K2+1) ≤ T2 ∧ T2 < 2^(K2+2))
  (hK3 : 2^(K3+1) ≤ T3 ∧ T3 < 2^(K3+2))
  (hK4 : 2^(K4+1) ≤ T4 ∧ T4 < 2^(K4+2))
  (h_step1 : K1 = K0 ∨ K1 = K0 + 1)
  (h_step2 : K2 = K1 ∨ K2 = K1 + 1)
  (h_step3 : K3 = K2 ∨ K3 = K2 + 1)
  (h_step4 : K4 = K3 ∨ K4 = K3 + 1)
  (hr0 : 183 * T0 ≤ 100 * T1 ∧ 500 * T1 ≤ 923 * T0)
  (hr1 : 183 * T1 ≤ 100 * T2 ∧ 500 * T2 ≤ 923 * T1)
  (hr2 : 183 * T2 ≤ 100 * T3 ∧ 500 * T3 ≤ 923 * T2)
  (hr3 : 183 * T3 ≤ 100 * T4 ∧ 500 * T4 ≤ 923 * T3)
  (ha0 : 3 * 2^K0 ≤ T0)
  (ha1 : 3 * 2^K1 ≤ T1)
  (ha2 : 3 * 2^K2 ≤ T2)
  (ha3 : 3 * 2^K3 ≤ T3)
  (ha4 : 3 * 2^K4 ≤ T4) :
  False := by
  rcases h_step1 with h1 | h1 <;> subst h1 <;>
  rcases h_step2 with h2 | h2 <;> subst h2 <;>
  rcases h_step3 with h3 | h3 <;> subst h3 <;>
  rcases h_step4 with h4 | h4 <;> subst h4
  all_goals
    simp only [pow_rewrite_1, pow_rewrite_2, pow_rewrite_3, pow_rewrite_4, pow_rewrite_5, pow_rewrite_6, pow_rewrite_7] at *
    try generalize 2^K0 = X at *
    try generalize 2^K1 = X at *
    try generalize 2^K2 = X at *
    try generalize 2^K3 = X at *
    try generalize 2^K4 = X at *
    omega


theorem tribonacci_ratio_inductive_step_tight (A B C : ℕ)
  (h1 : 183 * A ≤ 100 * B) (h2 : 500 * B ≤ 923 * A)
  (h3 : 183 * B ≤ 100 * C) (h4 : 500 * C ≤ 923 * B) :
  183 * C ≤ 100 * (C + B + A) ∧ 500 * (C + B + A) ≤ 923 * C := by
  omega
