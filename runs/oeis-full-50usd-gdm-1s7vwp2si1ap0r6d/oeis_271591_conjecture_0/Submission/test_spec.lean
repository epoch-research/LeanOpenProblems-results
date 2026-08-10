import FormalConjectures.Util.ProblemImports

open Nat

/--
The Tribonacci numbers $T_n$ (A000073).
$T_0=0, T_1=0, T_2=1$, and $T_n = T_{n-1} + T_{n-2} + T_{n-3}$ for $n \ge 3$.
-/
def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

/--
A271591: Second most significant bit of the tribonacci number A000073(n).
This is formalized by extracting the bit at position $\lfloor \log_2 T_n \rfloor - 1$.
-/
def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  -- The index of the MSB is T.log2. The index of the second MSB is T.log2 - 1.
  if h : T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

-- Definition for a maximal run of a value $v \in \{0, 1\}$ starting at index $n$ with length $L$.
-- We restrict $n \ge 2$ to account for "after the first two 0's" $a(0)=0, a(1)=0$.
def is_maximal_run (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  -- The run consists of L consecutive $v$'s starting at n
  (∀ i : ℕ, i < L → a (n + i) = v) ∧
  -- The run is not followed by $v$
  (a (n + L) ≠ v) ∧
  -- The run is not preceded by $v$
  (a (n - 1) ≠ v)

instance (v n L : ℕ) : Decidable (is_maximal_run v n L) := by
  unfold is_maximal_run
  infer_instance

-- Monotonicity of tribonacci
theorem tribonacci_mono (n : ℕ) : tribonacci n ≤ tribonacci (n + 1) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | n
  · decide
  · decide
  · decide
  · simp only [tribonacci]
    omega

theorem tribonacci_upper_bound (n : ℕ) (hn : n ≥ 5) : tribonacci (n + 1) ≤ 2 * tribonacci n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | _ | _ | n
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  rcases n with _ | _ | _ | n
  · decide
  · decide
  · decide
  · simp only [tribonacci]
    have h1 : tribonacci (n + 5) = tribonacci (n + 4) + tribonacci (n + 3) + tribonacci (n + 2) := by rfl
    have h2 : tribonacci (n + 6) = tribonacci (n + 5) + tribonacci (n + 4) + tribonacci (n + 3) := by rfl
    omega

theorem tribonacci_gt_one (n : ℕ) (hn : n ≥ 5) : tribonacci n > 1 := by
  have h : tribonacci 5 ≤ tribonacci n := by
    induction' n, hn using Nat.le_induction with k hk ih
    · rfl
    · have := tribonacci_mono k
      omega
  have h5 : tribonacci 5 = 4 := by rfl
  omega

lemma a_val (k : ℕ) : a k = 0 ∨ a k = 1 := by
  simp only [a]
  split_ifs
  · left; rfl
  · right; rfl
  · left; rfl

theorem tribonacci_ratio_inductive_step_tight (A B C : ℕ)
  (h1 : 183 * A ≤ 100 * B) (h2 : 500 * B ≤ 923 * A)
  (h3 : 183 * B ≤ 100 * C) (h4 : 500 * C ≤ 923 * B) :
  183 * C ≤ 100 * (C + B + A) ∧ 500 * (C + B + A) ≤ 923 * C := by
  omega

def ratio_bounds_tight (n : ℕ) : Prop :=
  183 * tribonacci n ≤ 100 * tribonacci (n + 1) ∧
  500 * tribonacci (n + 1) ≤ 923 * tribonacci n

def ratio_bounds_tight_two (n : ℕ) : Prop :=
  ratio_bounds_tight n ∧ ratio_bounds_tight (n + 1)

theorem tribonacci_ratio_bounds_tight_two (n : ℕ) (hn : n ≥ 8) : ratio_bounds_tight_two n := by
  induction' n, hn using Nat.le_induction with k hk ih
  · unfold ratio_bounds_tight_two ratio_bounds_tight
    decide
  · rcases ih with ⟨hk1, hk2⟩
    refine ⟨hk2, ?_⟩
    unfold ratio_bounds_tight
    have h_rec : tribonacci (k + 3) = tribonacci (k + 2) + tribonacci (k + 1) + tribonacci k := by rfl
    have h_ind := tribonacci_ratio_inductive_step_tight (tribonacci k) (tribonacci (k + 1)) (tribonacci (k + 2))
      hk1.1 hk1.2 hk2.1 hk2.2
    change 183 * tribonacci (k + 2) ≤ 100 * tribonacci (k + 3) ∧ 500 * tribonacci (k + 3) ≤ 923 * tribonacci (k + 2)
    rw [h_rec]
    exact h_ind

theorem tribonacci_ratio_bounds_tight (n : ℕ) (hn : n ≥ 8) : ratio_bounds_tight n := by
  have := tribonacci_ratio_bounds_tight_two n hn
  exact this.1

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

lemma log2_bounds (n : ℕ) (h : n ≠ 0) : 2^(n.log2) ≤ n ∧ n < 2^(n.log2 + 1) := by
  have h1 : 2^(n.log2) ≤ n := by
    rw [← Nat.le_log2 h]
  have h2 : n < 2^(n.log2 + 1) := by
    rw [← Nat.not_le, ← Nat.le_log2 h]
    omega
  exact ⟨h1, h2⟩

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

lemma K_step (T1 T2 K1 K2 : ℕ)
  (hT1_l : 2^(K1+1) ≤ T1) (hT1_u : T1 < 2^(K1+2))
  (hT2_l : 2^(K2+1) ≤ T2) (hT2_u : T2 < 2^(K2+2))
  (h_ratio_l : 9 * T1 ≤ 5 * T2) (h_ratio_u : 8 * T2 ≤ 15 * T1) :
  K2 = K1 ∨ K2 = K1 + 1 := by
  by_contra h_or
  push_neg at h_or
  by_cases hk : K2 < K1
  · have h_pow : 2^(K2 + 2) ≤ 2^(K1 + 1) := by
      apply Nat.pow_le_pow_right (by decide)
      omega
    omega
  · have h_pow : 2^(K1 + 3) ≤ 2^(K2 + 1) := by
      apply Nat.pow_le_pow_right (by decide)
      omega
    have h_pow1 : 2^(K1 + 2) = 4 * 2^K1 := by ring
    have h_pow2 : 2^(K1 + 3) = 8 * 2^K1 := by ring
    have h_pow3 : 2^(K2 + 2) = 2 * 2^(K2 + 1) := by ring
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

lemma log2_bounds' (m : ℕ) (hm : m ≥ 8) : 2^((tribonacci m).log2) ≤ tribonacci m ∧ tribonacci m < 2^((tribonacci m).log2 + 1) := by
  apply log2_bounds
  have : tribonacci m ≥ tribonacci 8 := by
    -- we can prove tribonacci 8 > 0
    -- and tribonacci m ≥ tribonacci 8 using monotonicity
    induction' m, hm using Nat.le_induction with k hk ih
    · rfl
    · have := tribonacci_mono k
      omega
  have h8 : tribonacci 8 = 44 := by rfl
  omega

lemma log2_sub_one (m : ℕ) (hm : m ≥ 8) : (tribonacci m).log2 ≥ 1 := by
  have hb := log2_bounds' m hm
  have : tribonacci m ≥ tribonacci 8 := by
    induction' m, hm using Nat.le_induction with k hk ih
    · rfl
    · have := tribonacci_mono k
      omega
  have h8 : tribonacci 8 = 44 := by rfl
  have : tribonacci m ≥ 44 := by omega
  have h_log : (tribonacci m).log2 ≥ 5 := by
    rw [Nat.le_log2 (by omega)]
    decide
  omega

lemma transition_0 (n : ℕ) (hn : n ≥ 8) (h_prev : a (n-1) = 1) (h_curr : a n = 0) :
  a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 0 := by
  have h_val1 : a (n+1) = 0 ∨ a (n+1) = 1 := a_val (n+1)
  have h_val2 : a (n+2) = 0 ∨ a (n+2) = 1 := a_val (n+2)
  have h_val3 : a (n+3) = 0 ∨ a (n+3) = 1 := a_val (n+3)
  
  have h_n1 : a (n+1) = 0 := by
    rcases h_val1 with h_n1 | h_n1
    · exact h_n1
    · -- contradiction using no_0_run_length_1_generalized
      -- let's construct the exponents
      have hn_prev : n - 1 ≥ 8 := by omega
      have hn_curr : n ≥ 8 := by omega
      have hn_next : n + 1 ≥ 8 := by omega
      
      let K_prev := (tribonacci (n-1)).log2 - 1
      let K_curr := (tribonacci n).log2 - 1
      let K_next := (tribonacci (n+1)).log2 - 1
      
      have h_bounds_prev : 2^(K_prev+1) ≤ tribonacci (n-1) ∧ tribonacci (n-1) < 2^(K_prev+2) := by
        have h_log : (tribonacci (n-1)).log2 - 1 = K_prev := rfl
        have hb := log2_bounds' (n-1) hn_prev
        have hl := log2_sub_one (n-1) hn_prev
        have : (tribonacci (n-1)).log2 = K_prev + 1 := by omega
        rw [this] at hb
        exact hb
        
      have h_bounds_curr : 2^(K_curr+1) ≤ tribonacci n ∧ tribonacci n < 2^(K_curr+2) := by
        have h_log : (tribonacci n).log2 - 1 = K_curr := rfl
        have hb := log2_bounds' n hn_curr
        have hl := log2_sub_one n hn_curr
        have : (tribonacci n).log2 = K_curr + 1 := by omega
        rw [this] at hb
        exact hb

      have h_bounds_next : 2^(K_next+1) ≤ tribonacci (n+1) ∧ tribonacci (n+1) < 2^(K_next+2) := by
        have h_log : (tribonacci (n+1)).log2 - 1 = K_next := rfl
        have hb := log2_bounds' (n+1) hn_next
        have hl := log2_sub_one (n+1) hn_next
        have : (tribonacci (n+1)).log2 = K_next + 1 := by omega
        rw [this] at hb
        exact hb

      have h_step1 : K_curr = K_prev ∨ K_curr = K_prev + 1 := by
        have h_ratio := tribonacci_ratio_bounds n (by omega)
        -- wait, tribonacci_ratio_bounds has ratio bounds 9 and 8
        -- and K_step expects these 9 and 8 bounds
        -- Let's check their types
        sorry
