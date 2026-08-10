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

lemma sum_pow_mod_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) :
  (∑ x ∈ range (c+1), p^x) % 2 = (c+1) % 2 := by
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hp_pow_odd (k : ℕ) : p^k % 2 = 1 := by rw [Nat.pow_mod, hp_odd, Nat.one_pow]
  induction c with
  | zero =>
    simp
  | succ c ih =>
    rw [sum_range_succ]
    rw [Nat.add_mod]
    rw [ih]
    rw [hp_pow_odd]
    omega

lemma odd_sigma_of_even_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : Even c) :
  ¬ 2 ∣ sigma 1 (p^c) := by
  rw [sigma_one_apply, Nat.divisors_prime_pow hp c]
  rw [sum_map]
  intro hdvd
  have h_mod : (∑ x ∈ range (c+1), p^x) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  rw [sum_pow_mod_two p hp hp2 c] at h_mod
  rcases hc with ⟨k, rfl⟩
  rw [← Nat.two_mul] at h_mod
  omega

lemma even_sigma_of_odd_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ Even c) :
  2 ∣ sigma 1 (p^c) := by
  rw [sigma_one_apply, Nat.divisors_prime_pow hp c]
  rw [sum_map]
  simp only [Function.Embedding.coeFn_mk]
  apply Nat.dvd_of_mod_eq_zero
  rw [sum_pow_mod_two p hp hp2 c]
  have h_odd : c % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
    · exfalso
      apply hc
      exact Nat.even_iff.mpr h0
    · exact h1
  omega

lemma padicVal_prime_power_neg_strong (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : c ≥ 1) :
  padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < 0 ∧
  (c ≥ 3 → padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) ≤ -padicValRat 2 (p+1 : ℚ) - 1) := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hc1 : c = 1
    · subst c
      have h1 := padicVal_prime_one_neg_lt_zero p hp hp2
      refine ⟨h1, ?_⟩
      intro h_ge3; exfalso; omega
    · by_cases hc2 : c = 2
      · subst c
        have ih_val_c1 := padicVal_prime_one_neg_lt_zero p hp hp2
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
          rw [padicValRat.add_eq_of_lt h_sum_nz h_sum1_nz h_term_nz (by rw [h_val_term]; rw [padicVal_prime_one_neg p hp hp2] at ih_val_c1; exact ih_val_c1)]
        have ih_val_c : padicValRat 2 (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
          rw [h_val_c]
          exact ih_val_c1
        refine ⟨ih_val_c, ?_⟩
        intro h_ge3; exfalso; omega
      · have hc_gt : c ≥ 3 := by omega
        by_cases h_even : Even c
        · -- Case A: c is even.
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
          have ih_strong_c_neg : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) ≤ -padicValRat 2 (p+1 : ℚ) - 1 := by
            rw [h_val_c]
            exact ih_strong_c1 (by omega)
          exact ⟨ih_val_c_neg, fun _ => ih_strong_c_neg⟩
        · -- Case B: c is odd.
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
          rcases hc_even with ⟨k, h_c_eq⟩
          have h_c_eq2 : c = 2*k + 1 := by omega
          have h_sum_pow : sigma 1 (p^c) = (p + 1) * ∑ i ∈ range (k + 1), p^(2*i) := by
            rw [h_c_eq2]
            rw [sigma_one_apply, Nat.divisors_prime_pow hp (2*k+1)]
            rw [sum_map]
            simp only [Function.Embedding.coeFn_mk]
            rw [sum_pow_pair p k]
          have h_cast_c : (sigma 1 (p^c) : ℚ) = ↑(sigma 1 (p^c)) := by rfl
          have h_sig_val_c : padicValRat 2 (sigma 1 (p^c) : ℚ) = padicValRat 2 (p+1 : ℚ) + padicValRat 2 (↑(∑ i ∈ range (k + 1), p^(2*i)) : ℚ) := by
            rw [h_cast_c]
            push_cast
            rw [h_sum_pow]
            push_cast
            rw [padicValRat.mul]
            · positivity
            · positivity
          have h_ge_p1 : padicValRat 2 (sigma 1 (p^c) : ℚ) ≥ padicValRat 2 (p+1 : ℚ) := by
            rw [h_sig_val_c]
            have h_ge_zero : padicValRat 2 (↑(∑ i ∈ range (k+1), p^(2*i)) : ℚ) ≥ 0 := by
              rw [← padicValRat_of_nat]
              exact_mod_cast Nat.zero_le (padicValNat 2 (∑ i ∈ range (k + 1), p ^ (2 * i)))
            omega
          have h_val_term_c : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^c))) ≤ -padicValRat 2 (p+1 : ℚ) := by
            rw [one_div]
            rw [padicValRat.inv]
            omega
          -- Now we do cases on c = 3
          by_cases hc3 : c = 3
          · subst c
            have h_sig_3 : sigma 1 (p^3) = (p+1) * (p^2+1) := by
              rw [sigma_one_apply, Nat.divisors_prime_pow hp 3]
              rw [sum_map]
              simp only [Function.Embedding.coeFn_mk]
              rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
              ring
            have h_p2_even : 2 ∣ (p^2+1) := by
              have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
              have h_eq : (p^2+1) % 2 = 0 := by
                rw [Nat.add_mod, Nat.pow_mod, hp_odd]
                rfl
              exact Nat.dvd_of_mod_eq_zero h_eq
            have h_p2_val : padicValRat 2 (p^2+1 : ℚ) ≥ 1 := by
              have h_cast : (p^2+1 : ℚ) = ↑(p^2+1) := by push_cast; rfl
              rw [h_cast, ← padicValRat_of_nat]
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
            have h_val_term_3 : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^3))) ≤ -padicValRat 2 (p+1 : ℚ) - 1 := by
              rw [one_div, padicValRat.inv, h_sig_3_val]
              omega
            -- padicValRat 2 S_2 = -v_2(p+1)
            have h_S2_val : padicValRat 2 (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) = -padicValRat 2 (p+1 : ℚ) := by
              have ih_val_c1_2 := padicVal_prime_one_neg_lt_zero p hp hp2
              have h_sum_c_2 : ∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j)) = (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^2)) := by
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
              rw [h_sum_c_2]
              have h_lt : padicValRat 2 (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) < padicValRat 2 ((1 : ℚ) / (sigma 1 (p^2))) := by
                rw [padicVal_prime_one_neg p hp hp2, h_val_term]
                exact padicVal_prime_one_neg_lt_zero p hp hp2
              rw [padicValRat.add_eq_of_lt h_sum_nz h_sum1_nz h_term_nz h_lt]
              exact padicVal_prime_one_neg p hp hp2
            -- Now we prove the result for S_3 using S_2 and T_3
            have h_sum1_pos : 0 < ∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j)) := by
              apply sum_pos
              · intro j hj
                have : (sigma 1 (p^j) : ℚ) > 0 := by
                  have : sigma 1 (p^j) > 0 := @sigma_pos 1 (p^j) (pow_ne_zero _ hp.ne_zero)
                  positivity
                positivity
              · rw [nonempty_range_iff]; omega
            have h_sum1_nz : (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) ≠ 0 := h_sum1_pos.ne'
            have h_term_pos : 0 < (1 : ℚ) / (sigma 1 (p^3)) := by
              have : (sigma 1 (p^3) : ℚ) > 0 := by
                have : sigma 1 (p^3) > 0 := @sigma_pos 1 (p^3) (pow_ne_zero _ hp.ne_zero)
                positivity
              positivity
            have h_term_nz : (1 : ℚ) / (sigma 1 (p^3)) ≠ 0 := h_term_pos.ne'
            have h_sum_nz : (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^3)) ≠ 0 := by
              apply (add_pos h_sum1_pos h_term_pos).ne'
            have h_lt : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^3))) < padicValRat 2 (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) := by
              rw [h_S2_val]
              omega
            have h_val_3 : padicValRat 2 (∑ j ∈ range 4, (1 : ℚ) / (sigma 1 (p^j))) = padicValRat 2 ((1 : ℚ) / (sigma 1 (p^3))) := by
              have h_sum_3_succ : ∑ j ∈ range 4, (1 : ℚ) / (sigma 1 (p^j)) = (∑ j ∈ range 3, (1 : ℚ) / (sigma 1 (p^j))) + (1 : ℚ) / (sigma 1 (p^3)) := by
                rw [sum_range_succ]
              rw [h_sum_3_succ]
              rw [add_comm]
              rw [padicValRat.add_eq_of_lt h_sum_nz h_term_nz h_sum1_nz h_lt]
            have h_val_3_neg : padicValRat 2 (∑ j ∈ range 4, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
              rw [h_val_3]
              omega
            have h_val_3_strong : padicValRat 2 (∑ j ∈ range 4, (1 : ℚ) / (sigma 1 (p^j))) ≤ -padicValRat 2 (p+1 : ℚ) - 1 := by
              rw [h_val_3]
              omega
            exact ⟨h_val_3_neg, fun _ => h_val_3_strong⟩
          · -- c >= 5
            have hc5 : c ≥ 5 := by omega
            have h_lt : padicValRat 2 (∑ j ∈ range c, (1 : ℚ) / (sigma 1 (p^j))) < padicValRat 2 ((1 : ℚ) / (sigma 1 (p^c))) := by
              omega
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
              rw [padicValRat.add_eq_of_lt h_sum_nz h_sum1_nz h_term_nz h_lt]
            have ih_val_c_neg : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
              rw [h_val_c]
              exact ih_val_c1
            have ih_strong_c_neg : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) ≤ -padicValRat 2 (p+1 : ℚ) - 1 := by
              rw [h_val_c]
              exact ih_strong_c1 (by omega)
            exact ⟨ih_val_c_neg, fun _ => ih_strong_c_neg⟩
