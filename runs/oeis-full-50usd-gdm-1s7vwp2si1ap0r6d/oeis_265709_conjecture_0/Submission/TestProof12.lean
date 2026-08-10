import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

lemma sum_pow_pair (p : ℕ) (k : ℕ) :
  ∑ x ∈ range (2*k + 2), p^x = (p + 1) * ∑ i ∈ range (k + 1), p^(2*i) := by
  induction k with
  | zero =>
    simp [sum_range_succ]
    omega
  | succ k ih =>
    have h1 : 2*(k+1) + 2 = 2*k + 2 + 2 := by omega
    rw [h1]
    rw [sum_range_add]
    rw [ih]
    have h2 : ∑ x ∈ range 2, p ^ (2 * k + 2 + x) = p^(2*k + 2) + p^(2*k + 3) := by
      rw [sum_range_succ, sum_range_one]
    rw [h2]
    have h3 : p^(2*k + 2) + p^(2*k + 3) = (p + 1) * p^(2*k + 2) := by
      have h_pow : p^(2*k + 3) = p^(2*k + 2) * p := by
        have h_eq : 2*k + 3 = (2*k + 2) + 1 := by omega
        rw [h_eq, pow_succ]
      rw [h_pow]
      ring
    rw [h3]
    rw [← mul_add]
    have h4 : ∑ i ∈ range (k + 2), p ^ (2 * i) = (∑ i ∈ range (k + 1), p ^ (2 * i)) + p^(2*k + 2) := by
      rw [sum_range_succ]
      have : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [this]
    rw [h4]

lemma padicVal_prime_one_neg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
  padicValRat 2 (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) = -padicValRat 2 (p+1 : ℚ) := by
  have h_sum : ∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j)) = (p + 2 : ℚ) / (p + 1 : ℚ) := by
    rw [sum_range_succ]
    rw [sum_range_one]
    simp only [pow_zero, pow_one]
    have hsigma1 : (sigma 1) 1 = 1 := by
      rw [sigma_one_apply, divisors_one, sum_singleton]
    rw [hsigma1]
    have hsigma_p : (sigma 1) p = p + 1 := by
      rw [sigma_one_apply, hp.divisors]
      have h1 : 1 ≠ p := hp.ne_one.symm
      rw [sum_insert (by simp [h1]), sum_singleton, add_comm]
    rw [hsigma_p]
    push_cast
    have hp1_pos : (p : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [h_sum]
  rw [padicValRat.div]
  · have h_cast : (p + 2 : ℚ) = ↑(p + 2) := by push_cast; rfl
    have h_num : padicValRat 2 (p + 2 : ℚ) = 0 := by
      rw [h_cast]
      rw [← padicValRat_of_nat]
      rw [← factorization_def _ Nat.prime_two]
      have h_odd : ¬ 2 ∣ (p + 2) := by
        intro hdvd
        have : 2 ∣ p := by omega
        have hp2_eq : p = 2 := (hp.eq_one_or_self_of_dvd 2 this).resolve_left (by decide) |>.symm
        exact hp2 hp2_eq
      rw [factorization_eq_zero_of_not_dvd h_odd]
      rfl
    rw [h_num, zero_sub]
  · positivity
  · positivity

lemma padicVal_prime_one_neg_lt_zero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
  padicValRat 2 (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
  rw [padicVal_prime_one_neg p hp hp2]
  have h_cast2 : (p + 1 : ℚ) = ↑(p + 1) := by push_cast; rfl
  have h_den : padicValRat 2 (p + 1 : ℚ) ≥ 1 := by
    rw [h_cast2]
    rw [← padicValRat_of_nat]
    rw [← factorization_def _ Nat.prime_two]
    have h_even : 2 ∣ (p + 1) := by
      have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
      have h_eq : (p + 1) % 2 = 0 := by
        rw [Nat.add_mod, hp_odd]
      exact Nat.dvd_of_mod_eq_zero h_eq
    have hp1_ne : p + 1 ≠ 0 := by omega
    have hp_le := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hp1_ne).mp h_even
    exact_mod_cast hp_le
  omega
