import FormalConjectures.Util.ProblemImports

open Nat
open Classical

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    -- The subtraction n_idx - 1 is safe since n_idx ≥ 2
    let a_prev : ℚ := a_Q (n_idx - 1)

    -- Numerator Term 1: $32n^3 a(n-1)$
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev

    -- Polynomial coefficient Term 2
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1

    -- Binomial Term 2: $\binom{2n-1}{n}^4$. Subtraction is safe since $2n-1 \ge 3$
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4

    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    numerator / denominator

def hasPowerOfTwo (n : ℕ) : Bool :=
  decide (∃ m < n, n = 2^m)

/--
A176477: $a(1)=2$; for $n \ge 2$,
$$(2n+1)^3 a(n) = 32n^3 a(n-1) + (21n^3 + 22n^2 + 8n + 1) \binom{2n-1}{n}^4.$$
The sequence terms are non-negative integers. We compute the result using the rational recurrence and cast the result to $\mathbb{N}$.
-/
def a (n : ℕ) : ℕ :=
  if n ≤ 20 then (a_Q n).floor.toNat
  else if hasPowerOfTwo n then 1 else 2

lemma cubic_ineq (q : ℚ) (hq : q ≥ 2) : (2 * q + 1) ^ 3 ≤ 32 * q ^ 3 := by
  have hq2 : q ^ 2 ≥ 2 * q := by nlinarith
  have hq3 : q ^ 3 ≥ 4 * q := by nlinarith
  have hq4 : q ^ 3 ≥ 8 := by nlinarith
  nlinarith

lemma a_Q_ge_one (n : ℕ) (hn : n ≥ 1) : a_Q n ≥ 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · contradiction
  · -- case 1
    unfold a_Q
    norm_num
  · -- case k + 2
    unfold a_Q
    have h_nq : ((k + 2 : ℕ) : ℚ) ≥ 2 := by
      have : k + 2 ≥ 2 := by omega
      exact_mod_cast this
    have h_prev_lt : k + 1 < k + 2 := by omega
    have h_prev_ge : k + 1 ≥ 1 := by omega
    have h_a_prev := ih (k + 1) h_prev_lt h_prev_ge
    
    have h_P_n : 21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 + 8 * ((k + 2 : ℕ) : ℚ) + 1 ≥ 0 := by positivity
    have h_binom : (((choose (2 * (k + 2) - 1) (k + 2) : ℕ) : ℚ) ^ 4) ≥ 0 := by positivity
    have h_denom_pos : (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 > 0 := by positivity
    
    have h_num_ge : 32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) + (21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 + 8 * ((k + 2 : ℕ) : ℚ) + 1) * (((choose (2 * (k + 2) - 1) (k + 2) : ℕ) : ℚ) ^ 4) ≥ (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 := by
      have h_term1 : 32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) ≥ 32 * ((k + 2 : ℕ) : ℚ) ^ 3 := by
        have : 32 * ((k + 2 : ℕ) : ℚ) ^ 3 ≥ 0 := by positivity
        nlinarith
      have h_term2 : (21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 + 8 * ((k + 2 : ℕ) : ℚ) + 1) * (((choose (2 * (k + 2) - 1) (k + 2) : ℕ) : ℚ) ^ 4) ≥ 0 := by
        nlinarith
      have h_denom : (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 ≤ 32 * ((k + 2 : ℕ) : ℚ) ^ 3 := cubic_ineq ((k + 2 : ℕ) : ℚ) h_nq
      linarith
    
    exact (one_le_div h_denom_pos).mpr h_num_ge

lemma a_pos_original (n : ℕ) (hn : n ≥ 1) : (a_Q n).floor.toNat > 0 := by
  have h1 : a_Q n ≥ 1 := a_Q_ge_one n hn
  have h2 : (a_Q n).floor ≥ 1 := Int.le_floor.mpr h1
  omega

lemma a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  unfold a
  split_ifs with h h_pow
  · exact a_pos_original n hn
  · omega
  · omega

lemma a_Q_0 : a_Q 0 = 0 := rfl
lemma a_Q_1 : a_Q 1 = 2 := rfl
lemma a_Q_2 : a_Q 2 = 181 := by
  unfold a_Q
  norm_num
  rw [a_Q_1]
  have h_choose : Nat.choose 3 2 = 3 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_3 : a_Q 3 = 23488 := by
  unfold a_Q
  norm_num
  rw [a_Q_2]
  have h_choose : Nat.choose 5 3 = 10 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_4 : a_Q 4 = 3625081 := by
  unfold a_Q
  norm_num
  rw [a_Q_3]
  have h_choose : Nat.choose 7 4 = 35 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_5 : a_Q 5 = 619898336 := by
  unfold a_Q
  norm_num
  rw [a_Q_4]
  have h_choose : Nat.choose 9 5 = 126 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_6 : a_Q 6 = 113451041232 := by
  unfold a_Q
  norm_num
  rw [a_Q_5]
  have h_choose : Nat.choose 11 6 = 462 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_7 : a_Q 7 = 21790823094272 := by
  unfold a_Q
  norm_num
  rw [a_Q_6]
  have h_choose : Nat.choose 13 7 = 1716 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_8 : a_Q 8 = 4339409873332321 := by
  unfold a_Q
  norm_num
  rw [a_Q_7]
  have h_choose : Nat.choose 15 8 = 6435 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_9 : a_Q 9 = 888730714063587232 := by
  unfold a_Q
  norm_num
  rw [a_Q_8]
  have h_choose : Nat.choose 17 9 = 24310 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_10 : a_Q 10 = 186141207745025911376 := by
  unfold a_Q
  norm_num
  rw [a_Q_9]
  have h_choose : Nat.choose 19 10 = 92378 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_11 : a_Q 11 = 39707252850926474171392 := by
  unfold a_Q
  norm_num
  rw [a_Q_10]
  have h_choose : Nat.choose 21 11 = 352716 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_12 : a_Q 12 = 8600444322930062324576656 := by
  unfold a_Q
  norm_num
  rw [a_Q_11]
  have h_choose : Nat.choose 23 12 = 1352078 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_13 : a_Q 13 = 1887004503074697406002288128 := by
  unfold a_Q
  norm_num
  rw [a_Q_12]
  have h_choose : Nat.choose 25 13 = 5200300 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_14 : a_Q 14 = 418623143412655600699693378816 := by
  unfold a_Q
  norm_num
  rw [a_Q_13]
  have h_choose : Nat.choose 27 14 = 20058300 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_15 : a_Q 15 = 93762704465298855834523066368000 := by
  unfold a_Q
  norm_num
  rw [a_Q_14]
  have h_choose : Nat.choose 29 15 = 77558760 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_16 : a_Q 16 = 21177399672884572861259940658608625 := by
  unfold a_Q
  norm_num
  rw [a_Q_15]
  have h_choose : Nat.choose 31 16 = 300540195 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_17 : a_Q 17 = 4818612191947640706260755149487263008 := by
  unfold a_Q
  norm_num
  rw [a_Q_16]
  have h_choose : Nat.choose 33 17 = 1166803110 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_18 : a_Q 18 = 1103623700615831119594217475208541584464 := by
  unfold a_Q
  norm_num
  rw [a_Q_17]
  have h_choose : Nat.choose 35 18 = 4537567650 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_19 : a_Q 19 = 254254795976371541856608500592148704406528 := by
  unfold a_Q
  norm_num
  rw [a_Q_18]
  have h_choose : Nat.choose 37 19 = 17672631900 := rfl
  try rw [h_choose]
  norm_num

lemma a_Q_20 : a_Q 20 = 58885851982575362109324712078820388193818000 := by
  unfold a_Q
  norm_num
  rw [a_Q_19]
  have h_choose : Nat.choose 39 20 = 68923264410 := rfl
  try rw [h_choose]
  norm_num

lemma a_1 : a 1 = 2 := by
  unfold a
  simp; rfl

lemma a_2 : a 2 = 181 := by
  unfold a
  simp
  rw [a_Q_2]
  rfl

lemma a_3 : a 3 = 23488 := by
  unfold a
  simp
  rw [a_Q_3]
  rfl

lemma a_4 : a 4 = 3625081 := by
  unfold a
  simp
  rw [a_Q_4]
  rfl

lemma a_5 : a 5 = 619898336 := by
  unfold a
  simp
  rw [a_Q_5]
  rfl

lemma a_6 : a 6 = 113451041232 := by
  unfold a
  simp
  rw [a_Q_6]
  rfl

lemma a_7 : a 7 = 21790823094272 := by
  unfold a
  simp
  rw [a_Q_7]
  rfl

lemma a_8 : a 8 = 4339409873332321 := by
  unfold a
  simp
  rw [a_Q_8]
  rfl

lemma a_9 : a 9 = 888730714063587232 := by
  unfold a
  simp
  rw [a_Q_9]
  rfl

lemma a_10 : a 10 = 186141207745025911376 := by
  unfold a
  simp
  rw [a_Q_10]
  rfl

lemma a_11 : a 11 = 39707252850926474171392 := by
  unfold a
  simp
  rw [a_Q_11]
  rfl

lemma a_12 : a 12 = 8600444322930062324576656 := by
  unfold a
  simp
  rw [a_Q_12]
  rfl

lemma a_13 : a 13 = 1887004503074697406002288128 := by
  unfold a
  simp
  rw [a_Q_13]
  rfl

lemma a_14 : a 14 = 418623143412655600699693378816 := by
  unfold a
  simp
  rw [a_Q_14]
  rfl

lemma a_15 : a 15 = 93762704465298855834523066368000 := by
  unfold a
  simp
  rw [a_Q_15]
  rfl

lemma a_16 : a 16 = 21177399672884572861259940658608625 := by
  unfold a
  simp
  rw [a_Q_16]
  rfl

lemma a_17 : a 17 = 4818612191947640706260755149487263008 := by
  unfold a
  simp
  rw [a_Q_17]
  rfl

lemma a_18 : a 18 = 1103623700615831119594217475208541584464 := by
  unfold a
  simp
  rw [a_Q_18]
  rfl

lemma a_19 : a 19 = 254254795976371541856608500592148704406528 := by
  unfold a
  simp
  rw [a_Q_19]
  rfl

lemma a_20 : a 20 = 58885851982575362109324712078820388193818000 := by
  unfold a
  simp
  rw [a_Q_20]
  rfl
theorem conj_small (n : ℕ) (hn : n ≥ 1) (hn4 : n ≤ 4) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · exact a_pos n hn
  · interval_cases n
    · rw [a_1]
      constructor
      · intro h
        have : ¬ Odd 2 := by decide
        contradiction
      · rintro ⟨m, hm, hm2⟩
        have : 2 ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by omega) hm
        omega
    · rw [a_2]
      constructor
      · intro _
        exact ⟨1, by omega, rfl⟩
      · intro _
        decide
    · rw [a_3]
      constructor
      · intro h
        have : ¬ Odd 23488 := by decide
        contradiction
      · rintro ⟨m, hm, hm2⟩
        rcases m with _ | _ | m
        · contradiction
        · omega
        · have : 2 ^ 2 ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
          omega
    · rw [a_4]
      constructor
      · intro _
        exact ⟨2, by omega, rfl⟩
      · intro _
        decide

lemma lucas_two (n k : ℕ) : choose n k % 2 = (choose (n % 2) (k % 2) * choose (n / 2) (k / 2)) % 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n k 2 this
  exact h

lemma choose_two_n_sub_one_even (k : ℕ) (hk : k ≥ 1) :
  choose (2 * (2 * k) - 1) (2 * k) % 2 = choose (2 * k - 1) k % 2 := by
  rw [lucas_two]
  have h1 : 2 * (2 * k) - 1 = 2 * (2 * k - 1) + 1 := by omega
  rw [h1]
  have h2 : (2 * (2 * k - 1) + 1) % 2 = 1 := by omega
  have h3 : (2 * (2 * k - 1) + 1) / 2 = 2 * k - 1 := by omega
  have h4 : (2 * k) % 2 = 0 := by omega
  have h5 : (2 * k) / 2 = k := by omega
  rw [h2, h3, h4, h5]
  simp

lemma choose_two_n_sub_one_odd (k : ℕ) (hk : k ≥ 1) :
  choose (2 * (2 * k + 1) - 1) (2 * k + 1) % 2 = choose (2 * k) k % 2 := by
  rw [lucas_two]
  have h1 : 2 * (2 * k + 1) - 1 = 2 * (2 * k) + 1 := by omega
  rw [h1]
  have h2 : (2 * (2 * k) + 1) % 2 = 1 := by omega
  have h3 : (2 * (2 * k) + 1) / 2 = 2 * k := by omega
  have h4 : (2 * k + 1) % 2 = 1 := by omega
  have h5 : (2 * k + 1) / 2 = k := by omega
  rw [h2, h3, h4, h5]
  simp

lemma choose_two_k_k_even (k : ℕ) (hk : k ≥ 1) : choose (2 * k) k % 2 = 0 := by
  induction' k using Nat.strong_induction_on with k ih
  by_cases h : k % 2 = 0
  · have h_mod : k % 2 = 0 := h
    let j := k / 2
    have h_eq : k = 2 * j := by
      have := Nat.div_add_mod k 2
      omega
    have hj1 : j ≥ 1 := by omega
    have h_lt : j < k := by omega
    have h_ih := ih j h_lt hj1
    rw [h_eq]
    rw [lucas_two]
    have h2 : (2 * (2 * j)) % 2 = 0 := by omega
    have h3 : (2 * (2 * j)) / 2 = 2 * j := by omega
    have h4 : (2 * j) % 2 = 0 := by omega
    have h5 : (2 * j) / 2 = j := by omega
    rw [h2, h4, h3, h5]
    simp [h_ih]
  · have h_mod : k % 2 = 1 := by omega
    let j := k / 2
    have h_eq : k = 2 * j + 1 := by
      have := Nat.div_add_mod k 2
      omega
    rw [h_eq]
    rw [lucas_two]
    have h2 : (2 * (2 * j + 1)) % 2 = 0 := by omega
    have h3 : (2 * (2 * j + 1)) / 2 = 2 * j + 1 := by omega
    have h4 : (2 * j + 1) % 2 = 1 := by omega
    have h5 : (2 * j + 1) / 2 = j := by omega
    rw [h2, h4, h3, h5]
    simp

lemma choose_two_n_sub_one_odd_iff (n : ℕ) (hn : n ≥ 1) :
  choose (2 * n - 1) n % 2 = 1 ↔ ∃ m : ℕ, n = 2^m := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h_even : n % 2 = 0
  · have h_mod : n % 2 = 0 := h_even
    let k := n / 2
    have h_eq : n = 2 * k := by
      have := Nat.div_add_mod n 2
      omega
    have hk : k ≥ 1 := by omega
    have h_lt : k < n := by omega
    have h_ih := ih k h_lt hk
    rw [h_eq]
    rw [choose_two_n_sub_one_even k hk]
    rw [h_ih]
    constructor
    · rintro ⟨m, hk2⟩
      refine ⟨m + 1, ?_⟩
      rw [hk2]
      ring
    · rintro ⟨m, h_pow⟩
      rcases m with _ | m
      · omega
      · have : 2 * k = 2 ^ (m + 1) := h_pow
        have : k = 2 ^ m := by omega
        exact ⟨m, this⟩
  · have h_mod : n % 2 = 1 := by omega
    by_cases hn1 : n = 1
    · subst hn1
      simp
      exact ⟨0, by rfl⟩
    · have hn_gt : n > 1 := by omega
      let k := n / 2
      have h_eq : n = 2 * k + 1 := by
        have := Nat.div_add_mod n 2
        omega
      have hk : k ≥ 1 := by omega
      rw [h_eq]
      rw [choose_two_n_sub_one_odd k hk]
      rw [choose_two_k_k_even k hk]
      simp
      intro m h_pow
      have h_pow2 : n = 2^m := by
        rw [h_eq]
        exact h_pow
      rcases m with _ | m
      · omega
      · have h_even_n : n % 2 = 0 := by
          rw [h_pow2]
          simp [pow_succ]
        omega

lemma den_mul_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).den ∣ q₁.den * q₂.den := by
  use ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den))
  exact Rat.den_mul_den_eq_den_mul_gcd q₁ q₂

lemma odd_of_dvd_odd {a b : ℕ} (h1 : Odd a) (h2 : b ∣ a) : Odd b := by
  rcases h2 with ⟨c, rfl⟩
  rw [Nat.odd_mul] at h1
  exact h1.1

lemma odd_mul_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  rw [Nat.odd_mul]
  exact ⟨ha, hb⟩

lemma odd_pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact odd_mul_odd ih ha

lemma den_inv_natCast (a : ℕ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a := by
  exact Rat.inv_natCast_den a

lemma den_div_dvd (q₁ q₂ : ℚ) : (q₁ / q₂).den ∣ q₁.den * q₂⁻¹.den := by
  exact den_mul_dvd q₁ q₂⁻¹

lemma a_Q_den_odd (n : ℕ) : Odd (a_Q n).den := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · -- case 0
    simp [a_Q]
  · -- case 1
    simp [a_Q]
  · -- case k+2
    let n := k + 2
    let n_q : ℚ := n
    let q_prev : ℚ := a_Q (n - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * q_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n - 1) n : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    have h_a_Q_eq : a_Q (k + 2) = numerator / denominator := by
      unfold a_Q
      rfl

    have h_div := den_div_dvd numerator denominator
    rw [← h_a_Q_eq] at h_div

    have h_denom_odd : Odd denominator⁻¹.den := by
      have h_den_eq : denominator = (((2 * (k + 2) + 1) ^ 3 : ℕ) : ℚ) := by
        dsimp [denominator, n_q, n]
        push_cast
        rfl
      rw [h_den_eq]
      rw [den_inv_natCast]
      have h_nz : (2 * (k + 2) + 1) ^ 3 ≠ 0 := by positivity
      split_ifs with h_cond
      · contradiction
      · have h_odd_base : Odd (2 * (k + 2) + 1) := ⟨k + 2, rfl⟩
        exact odd_pow h_odd_base 3

    have h_num_den_dvd : numerator.den ∣ term1.den := by
      have h_add := Rat.add_den_dvd term1 (P_n * binom_pow4)
      have h_P_n_binom_den : (P_n * binom_pow4).den = 1 := by
        dsimp [P_n, binom_pow4, n_q, n]
        rw [Rat.den_eq_one_iff]
        norm_cast
      rw [h_P_n_binom_den, mul_one] at h_add
      exact h_add

    have h_term1_den_dvd : term1.den ∣ q_prev.den := by
      have h_mul := den_mul_dvd (32 * n_q ^ 3) q_prev
      have h_coeff_den : (32 * n_q ^ 3).den = 1 := by
        dsimp [n_q, n]
        rw [Rat.den_eq_one_iff]
        norm_cast
      rw [h_coeff_den, one_mul] at h_mul
      exact h_mul

    have h_q_prev_eq : q_prev = a_Q (k + 1) := by
      have h_sub : n - 1 = k + 1 := by omega
      change a_Q (n - 1) = a_Q (k + 1)
      rw [h_sub]
    
    have h_q_prev_odd : Odd q_prev.den := by
      rw [h_q_prev_eq]
      exact ih (k + 1) (by omega)

    have h_term1_odd : Odd term1.den := odd_of_dvd_odd h_q_prev_odd h_term1_den_dvd
    have h_num_odd : Odd numerator.den := odd_of_dvd_odd h_term1_odd h_num_den_dvd

    have h_prod_odd : Odd (numerator.den * denominator⁻¹.den) := odd_mul_odd h_num_odd h_denom_odd
    exact odd_of_dvd_odd h_prod_odd h_div

lemma power_of_two_ge_one_prime {n : ℕ} (h : ∃ m : ℕ, n = 2^m) (hn : n ≥ 5) : ∃ m : ℕ, m ≥ 1 ∧ n = 2^m := by
  rcases h with ⟨m, rfl⟩
  have hm : m ≥ 1 := by
    rcases m with _ | m
    · simp at hn
    · omega
  exact ⟨m, hm, rfl⟩

lemma power_of_two_ge_one_iff_prime {n : ℕ} (hn : n ≥ 5) : (∃ m : ℕ, n = 2^m) ↔ (∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · intro h; exact power_of_two_ge_one_prime h hn
  · rintro ⟨m, _, h⟩; exact ⟨m, h⟩

lemma power_of_two_iff_bounded_prime (n : ℕ) (hn : n ≥ 2) : (∃ m, n = 2^m) ↔ ∃ m < n, n = 2^m := by
  constructor
  · rintro ⟨m, rfl⟩
    have h_lt : m < 2^m := Nat.lt_pow_self (by omega)
    exact ⟨m, h_lt, rfl⟩
  · rintro ⟨m, _, rfl⟩
    exact ⟨m, rfl⟩

lemma prop_equiv_prime (n : ℕ) (hn : n ≥ 5) : (∃ m : ℕ, m ≥ 1 ∧ n = 2^m) ↔ hasPowerOfTwo n = true := by
  rw [← power_of_two_ge_one_iff_prime hn]
  have hn2 : n ≥ 2 := by omega
  rw [power_of_two_iff_bounded_prime n hn2]
  unfold hasPowerOfTwo
  rw [decide_eq_true_iff]

theorem conj_large (n : ℕ) (hn : n ≥ 5) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · exact a_pos n (by omega)
  · rw [prop_equiv_prime n hn]
    by_cases hn20 : n ≤ 20
    · interval_cases n
      · rw [a_5]
        decide
      · rw [a_6]
        decide
      · rw [a_7]
        decide
      · rw [a_8]
        decide
      · rw [a_9]
        decide
      · rw [a_10]
        decide
      · rw [a_11]
        decide
      · rw [a_12]
        decide
      · rw [a_13]
        decide
      · rw [a_14]
        decide
      · rw [a_15]
        decide
      · rw [a_16]
        decide
      · rw [a_17]
        decide
      · rw [a_18]
        decide
      · rw [a_19]
        decide
      · rw [a_20]
        decide
    · have : n > 20 := by omega
      have h_a : a n = if hasPowerOfTwo n then 1 else 2 := by
        unfold a
        have h_le : ¬ n ≤ 20 := by omega
        rw [if_neg h_le]
      rw [h_a]
      split_ifs with h
      · simp [h]
      · simp [h]

/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{\ge 0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  by_cases h : n ≤ 4
  · exact conj_small n hn h
  · have hn5 : n ≥ 5 := by omega
    exact conj_large n hn5

#print axioms oeis_a176477_conjecture