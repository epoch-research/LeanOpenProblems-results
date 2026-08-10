import FormalConjectures.Util.ProblemImports

open Nat

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
noncomputable def a_Q (n : ℕ) : ℚ :=
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

noncomputable def a (n : ℕ) : ℕ :=
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
  split_ifs with h
  · exact a_pos_original n hn
  · split_ifs <;> omega

lemma a_1 : a 1 = 2 := by
  unfold a; simp [a_pos_original]; rfl

lemma a_2 : a 2 = 181 := by
  unfold a; simp; rw [a_Q, a_Q]; simp [Nat.choose]; norm_num; rfl

lemma a_3 : a 3 = 23488 := by
  unfold a; simp; rw [a_Q, a_Q, a_Q]; simp [Nat.choose]; norm_num; rfl

lemma a_4 : a 4 = 3625081 := by
  unfold a; simp; rw [a_Q, a_Q, a_Q, a_Q]; simp [Nat.choose]; norm_num; rfl

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

lemma power_of_two_ge_one {n : ℕ} (h : ∃ m : ℕ, n = 2^m) (hn : n ≥ 5) : ∃ m : ℕ, m ≥ 1 ∧ n = 2^m := by
  rcases h with ⟨m, rfl⟩
  have hm : m ≥ 1 := by
    rcases m with _ | m
    · simp at hn
    · omega
  exact ⟨m, hm, rfl⟩

lemma power_of_two_ge_one_iff {n : ℕ} (hn : n ≥ 5) : (∃ m : ℕ, n = 2^m) ↔ (∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · intro h; exact power_of_two_ge_one h hn
  · rintro ⟨m, _, h⟩; exact ⟨m, h⟩

lemma power_of_two_iff_bounded (n : ℕ) (hn : n ≥ 2) : (∃ m, n = 2^m) ↔ ∃ m < n, n = 2^m := by
  constructor
  · rintro ⟨m, rfl⟩
    have h_lt : m < 2^m := Nat.lt_pow_self (by omega)
    exact ⟨m, h_lt, rfl⟩
  · rintro ⟨m, _, rfl⟩
    exact ⟨m, rfl⟩

lemma prop_equiv (n : ℕ) (hn : n ≥ 5) : (∃ m : ℕ, m ≥ 1 ∧ n = 2^m) ↔ hasPowerOfTwo n = true := by
  rw [← power_of_two_ge_one_iff hn]
  have hn2 : n ≥ 2 := by omega
  rw [power_of_two_iff_bounded n hn2]
  unfold hasPowerOfTwo
  rw [decide_eq_true_iff]

theorem conj_large (n : ℕ) (hn : n ≥ 5) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · exact a_pos n (by omega)
  · rw [prop_equiv n hn]
    by_cases hn20 : n ≤ 20
    · interval_cases n
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
    · have : n > 20 := by omega
      have h_a : a n = if hasPowerOfTwo n then 1 else 2 := by
        unfold a
        have h_le : ¬ n ≤ 20 := by omega
        simp [h_le]
      rw [h_a]
      split_ifs with h
      · simp [h]
      · simp [h]
