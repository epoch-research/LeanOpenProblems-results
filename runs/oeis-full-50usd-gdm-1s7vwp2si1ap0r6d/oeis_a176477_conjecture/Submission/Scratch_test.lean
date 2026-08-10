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

lemma test_simp_den (n : ℕ) : ((n : ℚ)).den = 1 := by
  simp

lemma test_simp_den_pow (n : ℕ) : (((n : ℚ) ^ 4)).den = 1 := by
  simp

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



