import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

-- import Spec.lean's helpers
lemma odd_sigma_two_pow (k : ℕ) : ¬ 2 ∣ (sigma 1 (2^k)) := by
  sorry

lemma my_geom_sum_eq (a : ℕ) :
  ∑ x ∈ range a, (1 : ℚ) / 2^(x+1) = 1 - (1 / 2^a) := by
  sorry

lemma S_two_pow_bounds (a : ℕ) (ha : a ≥ 1) :
  1 < ∑ j ∈ range (a+1), (1 : ℚ) / (sigma 1 (2^j)) ∧
  ∑ j ∈ range (a+1), (1 : ℚ) / (sigma 1 (2^j)) < 2 := by
  sorry

lemma padicVal_prime_one_neg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
  padicValRat 2 (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
  sorry

lemma odd_sigma_of_even_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : Even c) :
  ¬ 2 ∣ sigma 1 (p^c) := by
  sorry

lemma even_sigma_of_odd_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ Even c) :
  2 ∣ sigma 1 (p^c) := by
  sorry

lemma padicVal_prime_power_neg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : c ≥ 1) :
  padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hc1 : c = 1
    · subst c
      exact padicVal_prime_one_neg p hp hp2
    · have hc_gt : c > 1 := by omega
      by_cases h_even : Even c
      · -- Case 1: c is even (so T_c has valuation 0). This is the easy case!
        have ih_val := ih (c-1) (by omega) (by omega)
        have h_eq : range (c - 1 + 1) = range c := by
          rw [Nat.sub_add_cancel (by omega)]
        rw [h_eq] at ih_val
        -- We write S_c = S_{c-1} + T_c
        have h_sum_c : ∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j)) = (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^c)) := by
          rw [sum_range_succ]
        have h_sig_odd : ¬ 2 ∣ sigma 1 (p^c) := odd_sigma_of_even_power p hp hp2 c h_even
        have h_cast : ((sigma 1 (p^c)) : ℚ) = ↑(sigma 1 (p^c)) := by rfl
        have h_sig_val : padicValRat 2 (sigma 1 (p^c) : ℚ) = 0 := by
          rw [h_cast]
          rw [← padicValRat_of_nat]
          rw [← factorization_def _ Nat.prime_two]
          rw [factorization_eq_zero_of_not_dvd h_sig_odd]
          rfl
        have h_val_term : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^c))) = 0 := by
          rw [one_div]
          rw [padicValRat.inv]
          rw [h_sig_val]
          rfl
        -- To avoid positivity timeout, we prove nonzeroness of parts using simple steps
        have h_sum1_pos : 0 < ∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j)) := by
          apply sum_pos
          · intro j hj
            have : (sigma 1 (p^j) : ℚ) > 0 := by
              have : sigma 1 (p^j) > 0 := @sigma_pos 1 (p^j) (pow_ne_zero _ hp.ne_zero)
              positivity
            positivity
          · rw [nonempty_range_iff]; omega
        have h_sum1_nz : (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) ≠ 0 := h_sum1_pos.ne'
        have h_term_pos : 0 < (1 : ℚ) / (sigma 1 (p^c)) := by
          have : (sigma 1 (p^c) : ℚ) > 0 := by
            have : sigma 1 (p^c) > 0 := @sigma_pos 1 (p^c) (pow_ne_zero _ hp.ne_zero)
            positivity
          positivity
        have h_term_nz : (1 : ℚ) / (sigma 1 (p^c)) ≠ 0 := h_term_pos.ne'
        have h_sum_nz : (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^c)) ≠ 0 := by
          apply (add_pos h_sum1_pos h_term_pos).ne'
        rw [h_sum_c]
        rw [padicValRat.add_eq_of_lt h_sum_nz h_sum1_nz h_term_nz (by rw [h_val_term]; exact ih_val)]
        exact ih_val
      · -- Case 2: c is odd (so T_c has valuation <= -1)
        -- Since c > 1 and c is odd, c >= 3.
        have hc_even : Even (c-1) := by
          -- since c is odd, c-1 is even
          rcases Nat.even_or_odd c with h | h
          · exfalso; exact h_even h
          · rcases h with ⟨k, rfl⟩
            use k
            omega
        sorry
