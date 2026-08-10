import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

lemma odd_sigma_two_pow (k : ℕ) : ¬ 2 ∣ (sigma 1 (2^k)) := by
  rw [sigma_one_apply, Nat.divisors_prime_pow Nat.prime_two k]
  rw [sum_map]
  rw [sum_range_succ']
  simp
  have h_sum : ∑ x ∈ range k, 2 ^ (x + 1) = 2 * ∑ x ∈ range k, 2 ^ x := by
    simp_rw [pow_succ]
    rw [← sum_mul]
    rw [mul_comm]
  rw [h_sum]
  rw [add_comm]
  rw [Nat.add_mul_mod_self_left]
  rfl

lemma my_geom_sum_eq (a : ℕ) :
  ∑ x ∈ range a, (1 : ℚ) / 2^(x+1) = 1 - (1 / 2^a) := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    rw [sum_range_succ]
    rw [ih]
    push_cast
    have h2a : (2^a : ℚ) ≠ 0 := by positivity
    have h_pow : (2^(a+1) : ℚ) = 2^a * 2 := by
      simp [pow_succ]
    rw [h_pow]
    generalize hX_eq : (2^a : ℚ) = X
    have hX : X ≠ 0 := by
      rw [← hX_eq]
      exact h2a
    field_simp
    ring

lemma S_two_pow_bounds (a : ℕ) (ha : a ≥ 1) :
  1 < ∑ j ∈ range (a+1), (1 : ℚ) / (sigma 1 (2^j)) ∧
  ∑ j ∈ range (a+1), (1 : ℚ) / (sigma 1 (2^j)) < 2 := by
  constructor
  · rw [sum_range_succ']
    simp
    apply sum_pos
    · intro j hj
      have h_sigma : (sigma 1) (2^(j+1)) > 0 := sigma_pos 1 (2^(j+1)) (pow_ne_zero _ (by omega))
      positivity
    · rw [nonempty_range_iff]; omega
  · rw [sum_range_succ']
    simp
    have h_bound : ∑ x ∈ range a, (1 : ℚ) / ↑((sigma 1) (2 ^ (x + 1))) ≤ ∑ x ∈ range a, (1 : ℚ) / 2^(x+1) := by
      apply sum_le_sum
      intro j hj
      have h2 : 2^(j+1) ≤ (sigma 1) (2^(j+1)) := by
        rw [sigma_one_apply]
        apply Finset.single_le_sum (f := fun x => x)
        · intro i hi; exact Nat.zero_le i
        · rw [Nat.mem_divisors]; exact ⟨dvd_rfl, by positivity⟩
      have h2_cast : (2^(j+1) : ℚ) ≤ ↑((sigma 1) (2^(j+1))) := by
        exact_mod_cast h2
      have h_sig_pos : (↑((sigma 1) (2^(j+1))) : ℚ) > 0 := by
        have : (sigma 1) (2^(j+1)) > 0 := sigma_pos 1 (2^(j+1)) (pow_ne_zero _ (by omega))
        positivity
      have h_two_pos : (2^(j+1) : ℚ) > 0 := by positivity
      exact one_div_le_one_div_of_le h_two_pos h2_cast
    have h_geom : ∑ x ∈ range a, (1 : ℚ) / 2^(x+1) < 1 := by
      rw [my_geom_sum_eq a]
      have h_div_pos : (1 / 2^a : ℚ) > 0 := by positivity
      exact sub_lt_self 1 h_div_pos
    have h_lt : ∑ x ∈ range a, (1 : ℚ) / ↑((sigma 1) (2 ^ (x + 1))) < 1 := h_bound.trans_lt h_geom
    simp_rw [inv_eq_one_div]
    linarith

lemma padicVal_prime_one_neg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
  padicValRat 2 (∑ j ∈ range 2, (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
  -- range 2 is {0, 1}
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
    have h_cast2 : (p + 1 : ℚ) = ↑(p + 1) := by push_cast; rfl
    have h_den : padicValRat 2 (p + 1 : ℚ) ≥ 1 := by
      rw [h_cast2]
      rw [← padicValRat_of_nat]
      rw [← factorization_def _ Nat.prime_two]
      have h_even : 2 ∣ (p + 1) := by
        -- since p is prime and p ≠ 2, p is odd
        have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
        have h_eq : (p + 1) % 2 = 0 := by
          rw [Nat.add_mod, hp_odd]
        exact Nat.dvd_of_mod_eq_zero h_eq
      -- since 2 ∣ p+1, factorization 2 (p+1) >= 1
      -- we can use factorization_prime_le_iff_dvd
      have hp1_ne : p + 1 ≠ 0 := by omega
      have hp_le := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hp1_ne).mp h_even
      exact_mod_cast hp_le
    omega
  · positivity
  · positivity



lemma coprime_pow_two_odd (b m : ℕ) (hm : ¬ 2 ∣ m) : (2^b).Coprime m := by
  apply Nat.Coprime.pow_left
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm























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

lemma padicVal_prime_power_neg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) (hc : c ≥ 1) :
  padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < 0 := by
  induction c with
  | zero => omega
  | succ c ih =>
    by_cases hc0 : c = 0
    · subst c
      exact padicVal_prime_one_neg p hp hp2
    · have hc_ge : c ≥ 1 := by omega
      have ih_val := ih hc_ge
      rw [sum_range_succ]
      by_cases h_even : Even (c+1)
      · have h_sig_odd : ¬ 2 ∣ sigma 1 (p^(c+1)) := odd_sigma_of_even_power p hp hp2 (c+1) h_even
        have h_val_term : padicValRat 2 ((1 : ℚ) / (sigma 1 (p^(c+1)))) = 0 := by
          -- since sigma is odd, its valuation is 0, so 1/sigma has valuation 0
          sorry
        have h_lt : padicValRat 2 (∑ j ∈ range (c+1), (1 : ℚ) / (sigma 1 (p^j))) < padicValRat 2 ((1 : ℚ) / (sigma 1 (p^(c+1)))) := by
          omega
        -- now use add_eq_of_lt
        sorry
      · -- c+1 is odd, so c is even and c ≥ 1
        have hc_even : Even c := by
          -- since ¬ Even (c+1), c is even
          rcases hc_ge with h_pred | h_pred
          sorry
        sorry
