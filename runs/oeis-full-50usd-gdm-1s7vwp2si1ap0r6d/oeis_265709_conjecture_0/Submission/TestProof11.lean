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
  padicValRat 2 (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
  sorry

lemma odd_sigma_of_even_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : Even c) :
  ¬ 2 ∣ sigma 1 (p^c) := by
  sorry

lemma even_sigma_of_odd_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ Even c) :
  2 ∣ sigma 1 (p^c) := by
  sorry

lemma padicVal_prime_power_neg_strong (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : c ≥ 1) :
  padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < 0 ∧
  (c ≥ 3 → padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) ≤ -padicValRat 2 (p+1) - 1) := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hc1 : c = 1
    · subst c
      have h1 := padicVal_prime_one_neg p hp hp2
      refine ⟨h1, ?_⟩
      intro h_ge3; exfalso; omega
    · by_cases hc2 : c = 2
      · subst c
        -- S_2 = S_1 + T_2
        -- v_2(S_1) = -v_2(p+1) < 0
        -- v_2(T_2) = 0
        have ih_val_c1 := padicVal_prime_one_neg p hp hp2
        have h_sum_c : ∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j)) = (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^2)) := by
          rw [sum_range_succ]
        have h_even_2 : Even 2 := by use 1
        have h_sig_odd : ¬ 2 ∣ sigma 1 (p^2) := odd_sigma_of_even_power p hp hp2 2 h_even_2
        have h_cast : ((sigma 1 (p^2)) : ℚ) = ↑(sigma 1 (p^2)) := by rfl
        have h_sig_val : padicValRat 2 (sigma 1 (p^2) : ℚ) = 0 := by
          rw [h_cast]
          rw [← padicValRat_of_nat]
          rw [← factorization_def _ Nat.prime_two]
          rw [factorization_eq_zero_of_not_dvd h_sig_odd]
          rfl
        have h_val_term : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^2))) = 0 := by
          rw [one_div]
          rw [padicValRat.inv]
          rw [h_sig_val]
          rfl
        have h_sum1_pos : 0 < ∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j)) := by
          apply sum_pos
          · intro j hj
            have : (sigma 1 (p^j) : ℚ) > 0 := by
              have : sigma 1 (p^j) > 0 := @sigma_pos 1 (p^j) (pow_ne_zero _ hp.ne_zero)
              positivity
            positivity
          · rw [nonempty_range_iff]; omega
        have h_sum1_nz : (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) ≠ 0 := h_sum1_pos.ne'
        have h_term_pos : 0 < (1 : ℚ) / (sigma 1 (p^2)) := by
          have : (sigma 1 (p^2) : ℚ) > 0 := by
            have : sigma 1 (p^2) > 0 := @sigma_pos 1 (p^2) (pow_ne_zero _ hp.ne_zero)
            positivity
          positivity
        have h_term_nz : (1 : ℚ) / (sigma 1 (p^2)) ≠ 0 := h_term_pos.ne'
        have h_sum_nz : (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^2)) ≠ 0 := by
          apply (add_pos h_sum1_pos h_term_pos).ne'
        have h_val_c : padicValRat 2 (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) = padicValRat 2 (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) := by
          rw [h_sum_c]
          rw [padicValRat.add_eq_of_lt h_sum_nz h_sum1_nz h_term_nz (by rw [h_val_term]; exact ih_val_c1)]
        have ih_val_c : padicValRat 2 (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
          rw [h_val_c]
          exact ih_val_c1
        refine ⟨ih_val_c, ?_⟩
        intro h_ge3; exfalso; omega
      · have hc_gt : c ≥ 3 := by omega
        by_cases h_even : Even c
        · -- Case A: c is even.
          -- S_c = S_{c-1} + T_c where T_c has valuation 0.
          have ih_c1 := ih (c-1) (by omega) (by omega)
          have h_eq : range (c - 1 + 1) = range c := by
            rw [Nat.sub_add_cancel (by omega)]
          have ih_val_c1 := ih_c1.1
          rw [h_eq] at ih_val_c1
          have ih_strong_c1 := ih_c1.2
          rw [h_eq] at ih_strong_c1
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
          have h_val_c : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) = padicValRat 2 (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) := by
            rw [h_sum_c]
            rw [padicValRat.add_eq_of_lt h_sum_nz h_sum1_nz h_term_nz (by rw [h_val_term]; exact ih_val_c1)]
          have ih_val_c_neg : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
            rw [h_val_c]
            exact ih_val_c1
          have ih_strong_c_neg : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) ≤ -padicValRat 2 (p+1) - 1 := by
            rw [h_val_c]
            exact ih_strong_c1 (by omega)
          exact ⟨ih_val_c_neg, fun _ => ih_strong_c_neg⟩
        · -- Case B: c is odd.
          -- Since c is odd and c >= 3.
          have hc_even : Even (c-1) := by
            rcases Nat.even_or_odd c with h | h
            · exfalso; exact h_even h
            · rcases h with ⟨k, rfl⟩
              use k
              omega
          have ih_c1 := ih (c-1) (by omega) (by omega)
          have h_eq : range (c - 1 + 1) = range c := by
            rw [Nat.sub_add_cancel (by omega)]
          have ih_val_c1 := ih_c1.1
          rw [h_eq] at ih_val_c1
          have ih_strong_c1 := ih_c1.2
          rw [h_eq] at ih_strong_c1
          -- S_c = S_{c-1} + T_c
          have h_sum_c : ∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j)) = (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^c)) := by
            rw [sum_range_succ]
          have h_sig_even : 2 ∣ sigma 1 (p^c) := even_sigma_of_odd_power p hp hp2 c h_even
          -- We use sum_pow_pair to show padicValRat 2 (sigma 1 (p^c)) >= padicValRat 2 (p+1)
          rcases h_even with ⟨k, rfl⟩
          -- c = 2*k + 1
          -- sigma 1 (p^(2*k+1))
          have h_sum_pow : sigma 1 (p^(2*k+1)) = (p + 1) * ∑ i ∈ range (k + 1), p^(2*i) := by
            rw [sigma_one_apply, Nat.divisors_prime_pow hp (2*k+1)]
            rw [sum_pow_pair p k]
          have h_cast_c : (sigma 1 (p^(2*k+1)) : ℚ) = ↑(sigma 1 (p^(2*k+1))) := by rfl
          have h_sig_val_c : padicValRat 2 (sigma 1 (p^(2*k+1)) : ℚ) = padicValRat 2 (p+1 : ℚ) + padicValRat 2 (↑(∑ i ∈ range (k + 1), p^(2*i)) : ℚ) := by
            rw [h_cast_c]
            push_cast
            rw [h_sum_pow]
            push_cast
            rw [padicValRat.mul]
            · positivity
            · positivity
          have h_ge_p1 : padicValRat 2 (sigma 1 (p^(2*k+1)) : ℚ) ≥ padicValRat 2 (p+1 : ℚ) := by
            rw [h_sig_val_c]
            have h_ge_zero : padicValRat 2 (↑(∑ i ∈ range (k+1), p^(2*i)) : ℚ) ≥ 0 := by
              rw [← padicValRat_of_nat]
              exact_mod_cast zero_le (padicValNat 2 (∑ i ∈ range (k + 1), p ^ (2 * i)))
            omega
          have h_val_term_c : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^(2*k+1)))) ≤ -padicValRat 2 (p+1) := by
            rw [one_div]
            rw [padicValRat.inv]
            omega
          -- Now we do cases on c = 3
          by_cases hc3 : 2*k+1 = 3
          · -- c = 3. S_3 = S_2 + T_3
            -- v_2(S_2) = -v_2(p+1)
            -- v_2(T_3) <= -v_2(p+1) - 1
            -- So v_2(S_2) > v_2(T_3)
            -- So v_2(S_3) = v_2(T_3) <= -v_2(p+1) - 1
            have hk1 : k = 1 := by omega
            subst k
            have h_sig_3 : sigma 1 (p^3) = (p+1) * (p^2+1) := by
              rw [sigma_one_apply, Nat.divisors_prime_pow hp 3]
              rw [sum_map]
              simp
            have h_p2_even : 2 ∣ (p^2+1) := by
              have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
              have h_eq : (p^2+1) % 2 = 0 := by
                rw [Nat.add_mod, Nat.pow_mod, hp_odd]
                rfl
              exact Nat.dvd_of_mod_eq_zero h_eq
            have h_p2_val : padicValRat 2 (p^2+1 : ℚ) ≥ 1 := by
              rw [← padicValRat_of_nat]
              have h_ne : p^2+1 ≠ 0 := by positivity
              have h_le := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two h_ne).mp h_p2_even
              exact_mod_cast h_le
            have h_cast_3 : (sigma 1 (p^3) : ℚ) = ↑(sigma 1 (p^3)) := by rfl
            have h_sig_3_val : padicValRat 2 (sigma 1 (p^3) : ℚ) = padicValRat 2 (p+1 : ℚ) + padicValRat 2 (p^2+1 : ℚ) := by
              rw [h_cast_3]
              push_cast
              rw [h_sig_3]
              push_cast
              rw [padicValRat.mul]
              · positivity
              · positivity
            have h_val_term_3 : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^3))) ≤ -padicValRat 2 (p+1) - 1 := by
              rw [one_div, padicValRat.inv, h_sig_3_val]
              omega
            -- What is S_2's valuation? S_2 = S_1 + T_2. So v_2(S_2) = v_2(S_1) = -v_2(p+1)
            -- Let's prove v_2(S_2) = -v_2(p+1)
            have h_S2_val : padicValRat 2 (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) = -padicValRat 2 (p+1) := by
              -- S_2 is the sum over range 3
              -- we already proved this is equal to padicValRat 2 (S_1)
              -- which has valuation -v_2(p+1)
              -- Wait, is padicValRat 2 (S_1) = -v_2(p+1)?
              -- Let's check!
              sorry
            sorry
          · -- c >= 5
            sorry
