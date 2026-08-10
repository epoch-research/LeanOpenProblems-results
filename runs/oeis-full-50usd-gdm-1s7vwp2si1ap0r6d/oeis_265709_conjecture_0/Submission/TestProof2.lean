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
      by_cases h_even : Even (c+1)
      · -- Case 1: c+1 is even (so c is odd)
        -- We write S_{c+1} = S_c + T_{c+1} where T_{c+1} has valuation 0.
        have ih_val := ih c (by omega) (by omega)
        rw [sum_range_succ]
        have h_sig_odd : ¬ 2 ∣ sigma 1 (p^(c+1)) := odd_sigma_of_even_power p hp hp2 (c+1) h_even
        have h_cast : ((sigma 1 (p^(c+1))) : ℚ) = ↑(sigma 1 (p^(c+1))) := by rfl
        have h_sig_val : padicValRat 2 (sigma 1 (p^(c+1)) : ℚ) = 0 := by
          rw [h_cast]
          rw [← padicValRat_of_nat]
          rw [← factorization_def _ Nat.prime_two]
          rw [factorization_eq_zero_of_not_dvd h_sig_odd]
          rfl
        have h_val_term : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^(c+1)))) = 0 := by
          rw [one_div]
          rw [padicValRat.inv]
          rw [h_sig_val]
          rfl
        have h_sum_nz : (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^(c+1))) ≠ 0 := by positivity
        have h_sum1_nz : (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) ≠ 0 := by positivity
        have h_term_nz : (1 : ℚ) / (sigma 1 (p^(c+1))) ≠ 0 := by positivity
        rw [padicValRat.add_eq_of_lt h_sum_nz h_sum1_nz h_term_nz (by rw [h_val_term]; exact ih_val)]
        exact ih_val
      · -- Case 2: c+1 is odd (so c is even)
        -- Since c > 1 and c is even, c >= 2.
        have hc_even : Even c := by
          rcases Nat.even_or_odd c with h | h
          · exact h
          · exfalso
            apply h_even
            rcases h with ⟨k, rfl⟩
            use k + 1
            omega
        have ih_c1 : padicValRat 2 (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
          have h_c1 : c - 1 < c := by omega
          have h_c1_ge : c - 1 ≥ 1 := by omega
          have ih_val_c1 := ih (c-1) h_c1 h_c1_ge
          have h_eq : range (c - 1 + 1) = range c := by
            rw [Nat.sub_add_cancel (by omega)]
          rw [h_eq] at ih_val_c1
          exact ih_val_c1
        have h_sig_odd : ¬ 2 ∣ sigma 1 (p^c) := odd_sigma_of_even_power p hp hp2 c hc_even
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
        have h_sum_c : ∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j)) = (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^c)) := by
          rw [sum_range_succ]
        have h_sum_nz : (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^c)) ≠ 0 := by positivity
        have h_sum1_nz : (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) ≠ 0 := by positivity
        have h_term_nz : (1 : ℚ) / (sigma 1 (p^c)) ≠ 0 := by positivity
        have h_val_c : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) = padicValRat 2 (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) := by
          rw [h_sum_c]
          rw [padicValRat.add_eq_of_lt h_sum_nz h_sum1_nz h_term_nz (by rw [h_val_term]; exact ih_c1)]
        have ih_val_c : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
          rw [h_val_c]
          exact ih_c1
        -- Now we have S_c's valuation is ih_val_c < 0.
        -- We want S_{c+1} = S_c + T_{c+1} has valuation < 0.
        -- We do cases on whether v_2(S_c) < v_2(T_{c+1}) or not.
        rw [sum_range_succ]
        by_cases h_lt : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < padicValRat 2 ((1 : ℚ) / (sigma 1 (p^(c+1))))
        · have h_sum2_nz : (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^(c+1))) ≠ 0 := by positivity
          have h_sum3_nz : (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) ≠ 0 := by positivity
          have h_term2_nz : (1 : ℚ) / (sigma 1 (p^(c+1))) ≠ 0 := by positivity
          rw [padicValRat.add_eq_of_lt h_sum2_nz h_sum3_nz h_term2_nz h_lt]
          exact ih_val_c
        · by_cases h_gt : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) > padicValRat 2 ((1 : ℚ) / (sigma 1 (p^(c+1))))
          · have h_sum2_nz : (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^(c+1))) ≠ 0 := by positivity
            have h_sum3_nz : (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) ≠ 0 := by positivity
            have h_term2_nz : (1 : ℚ) / (sigma 1 (p^(c+1))) ≠ 0 := by positivity
            have h_add := padicValRat.add_eq_of_lt (p := 2) (y := (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j)))) h_sum2_nz h_term2_nz h_sum3_nz h_gt
            rw [add_comm] at h_add
            rw [h_add]
            omega
          · -- Case: they are equal. But we know they cannot be equal.
            -- Actually, if we cannot prove they are unequal, can we prove that v_2(T_{c+1}) <= -1,
            -- and then since they are equal, v_2(S_c) <= -1.
            -- Wait, if they are equal, then v_2(S_c) = v_2(T_{c+1}) = V <= -1.
            -- Since S_c > 0 and T_{c+1} > 0, they cannot cancel to 0.
            -- But we still need an upper bound on their sum.
            -- Let's see if we can prove they are unequal!
            sorry
