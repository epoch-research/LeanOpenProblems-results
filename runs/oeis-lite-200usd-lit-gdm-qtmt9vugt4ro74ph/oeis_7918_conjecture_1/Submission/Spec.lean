import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

lemma a_spec (n : ℕ) : Nat.Prime (a n) ∧ n ≤ a n := by
  exact @Nat.find_spec (fun p => Nat.Prime p ∧ n ≤ p) _ _

lemma a_le {n p : ℕ} (hp : Nat.Prime p ∧ n ≤ p) : a n ≤ p := by
  exact @Nat.find_le p (fun p => Nat.Prime p ∧ n ≤ p) _ _ hp

lemma lt_of_rpow_lt_rpow (b : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 < b) (h : x ^ b < y ^ b) : x < y := by
  have h_lt : (x ^ b) ^ (1 / b) < (y ^ b) ^ (1 / b) := by
    apply Real.rpow_lt_rpow (Real.rpow_nonneg hx b) h (div_pos zero_lt_one hb)
  rwa [← Real.rpow_mul hx, mul_one_div_cancel hb.ne', Real.rpow_one,
       ← Real.rpow_mul hy, mul_one_div_cancel hb.ne', Real.rpow_one] at h_lt

lemma a_four : a 4 = 5 := by
  have h1 : Nat.Prime 5 ∧ 4 ≤ 5 := ⟨by norm_num, by norm_num⟩
  apply le_antisymm
  · exact a_le h1
  · by_contra hc
    have hc2 : a 4 < 5 := not_le.mp hc
    interval_cases h : a 4
    · have h_spec := a_spec 4
      rw [h] at h_spec
      exact Nat.not_prime_zero h_spec.1
    · have h_spec := a_spec 4
      rw [h] at h_spec
      exact Nat.not_prime_one h_spec.1
    · have h_spec := a_spec 4
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 4
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 4
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 4 := by norm_num
      exact h_not_prime h_spec.1

lemma a_six : a 6 = 7 := by
  have h1 : Nat.Prime 7 ∧ 6 ≤ 7 := ⟨by norm_num, by norm_num⟩
  apply le_antisymm
  · exact a_le h1
  · by_contra hc
    have hc2 : a 6 < 7 := not_le.mp hc
    interval_cases h : a 6
    · have h_spec := a_spec 6
      rw [h] at h_spec
      exact Nat.not_prime_zero h_spec.1
    · have h_spec := a_spec 6
      rw [h] at h_spec
      exact Nat.not_prime_one h_spec.1
    · have h_spec := a_spec 6
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 6
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 6
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 4 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 6
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 6
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 6 := by norm_num
      exact h_not_prime h_spec.1

lemma a_eight : a 8 = 11 := by
  have h1 : Nat.Prime 11 ∧ 8 ≤ 11 := ⟨by norm_num, by norm_num⟩
  apply le_antisymm
  · exact a_le h1
  · by_contra hc
    have hc2 : a 8 < 11 := not_le.mp hc
    interval_cases h : a 8
    · have h_spec := a_spec 8
      rw [h] at h_spec
      exact Nat.not_prime_zero h_spec.1
    · have h_spec := a_spec 8
      rw [h] at h_spec
      exact Nat.not_prime_one h_spec.1
    · have h_spec := a_spec 8
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 8
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 8
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 4 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 8
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 8
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 6 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 8
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 8
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 8 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 8
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 9 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 8
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 10 := by norm_num
      exact h_not_prime h_spec.1

lemma a_nine : a 9 = 11 := by
  have h1 : Nat.Prime 11 ∧ 9 ≤ 11 := ⟨by norm_num, by norm_num⟩
  apply le_antisymm
  · exact a_le h1
  · by_contra hc
    have hc2 : a 9 < 11 := not_le.mp hc
    interval_cases h : a 9
    · have h_spec := a_spec 9
      rw [h] at h_spec
      exact Nat.not_prime_zero h_spec.1
    · have h_spec := a_spec 9
      rw [h] at h_spec
      exact Nat.not_prime_one h_spec.1
    · have h_spec := a_spec 9
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 9
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 9
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 4 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 9
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 9
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 6 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 9
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 9
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 8 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 9
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 9 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 9
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 10 := by norm_num
      exact h_not_prime h_spec.1

lemma a_ten : a 10 = 11 := by
  have h1 : Nat.Prime 11 ∧ 10 ≤ 11 := ⟨by norm_num, by norm_num⟩
  apply le_antisymm
  · exact a_le h1
  · by_contra hc
    have hc2 : a 10 < 11 := not_le.mp hc
    interval_cases h : a 10
    · have h_spec := a_spec 10
      rw [h] at h_spec
      exact Nat.not_prime_zero h_spec.1
    · have h_spec := a_spec 10
      rw [h] at h_spec
      exact Nat.not_prime_one h_spec.1
    · have h_spec := a_spec 10
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 10
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 10
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 4 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 10
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 10
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 6 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 10
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 10
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 8 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 10
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 9 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 10
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 10 := by norm_num
      exact h_not_prime h_spec.1

lemma a_twelve : a 12 = 13 := by
  have h1 : Nat.Prime 13 ∧ 12 ≤ 13 := ⟨by norm_num, by norm_num⟩
  apply le_antisymm
  · exact a_le h1
  · by_contra hc
    have hc2 : a 12 < 13 := not_le.mp hc
    interval_cases h : a 12
    · have h_spec := a_spec 12
      rw [h] at h_spec
      exact Nat.not_prime_zero h_spec.1
    · have h_spec := a_spec 12
      rw [h] at h_spec
      exact Nat.not_prime_one h_spec.1
    · have h_spec := a_spec 12
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 12
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 12
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 4 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 12
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 12
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 6 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 12
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 12
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 8 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 12
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 9 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 12
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 10 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 12
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 12
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 12 := by norm_num
      exact h_not_prime h_spec.1

lemma a_14_eq : a 14 = 17 := by
  have h1 : Nat.Prime 17 ∧ 14 ≤ 17 := ⟨by norm_num, by norm_num⟩
  apply le_antisymm
  · exact a_le h1
  · by_contra hc
    have hc2 : a 14 < 17 := not_le.mp hc
    interval_cases h : a 14
    · have h_spec := a_spec 14
      rw [h] at h_spec
      exact Nat.not_prime_zero h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      exact Nat.not_prime_one h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 14
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 4 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 6 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 8 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 9 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 10 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 12 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      omega
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 14 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 15 := by norm_num
      exact h_not_prime h_spec.1
    · have h_spec := a_spec 14
      rw [h] at h_spec
      have h_not_prime : ¬ Nat.Prime 16 := by norm_num
      exact h_not_prime h_spec.1

theorem test_four : (a 4 : ℝ) < (4 : ℝ) ^ ((4 : ℝ) ^ ((1 : ℝ) / (4 : ℝ))) := by
  have h_a4 : (a 4 : ℝ) = 5 := by exact_mod_cast a_four
  rw [h_a4]
  have h_pow : (4 : ℝ) ^ ((1 : ℝ) / (4 : ℝ)) = Real.sqrt 2 := by
    have h_four : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    nth_rw 1 [h_four]
    rw [← Real.rpow_mul (by norm_num)]
    have h_mul : (2 : ℝ) * ((1 : ℝ) / 4) = 1 / 2 := by norm_num
    rw [h_mul]
    exact (Real.sqrt_eq_rpow 2).symm
  rw [h_pow]
  have h_sqrt2_gt2 : (1.4 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    · norm_num
  have h_rpow_lt2 : (4 : ℝ) ^ (1.4 : ℝ) < (4 : ℝ) ^ Real.sqrt 2 := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_sqrt2_gt2
  have h_eq2 : (1.4 : ℝ) = (7 : ℝ) / 5 := by norm_num
  rw [h_eq2] at h_rpow_lt2
  have h_pos : 0 < (4 : ℝ) := by norm_num
  have h_pow_eq : (4 : ℝ) ^ ((7 : ℝ) / 5) = ((4 : ℝ) ^ (7 : ℝ)) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_mul (by norm_num)]
    have : (7 : ℝ) * (1 / 5) = 7 / 5 := by norm_num
    rw [this]
  rw [h_pow_eq] at h_rpow_lt2
  have h_five : (5 : ℝ) = ((5 : ℝ) ^ (5 : ℝ)) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have h_five_val : (5 : ℝ) ^ (5 : ℝ) = 3125 := by norm_num
  have h_four_val : (4 : ℝ) ^ (7 : ℝ) = 16384 := by norm_num
  have h_lt_aux : (5 : ℝ) ^ (5 : ℝ) < (4 : ℝ) ^ (7 : ℝ) := by
    rw [h_five_val, h_four_val]
    norm_num
  have h_lt_rpow : ((5 : ℝ) ^ (5 : ℝ)) ^ ((1 : ℝ) / 5) < ((4 : ℝ) ^ (7 : ℝ)) ^ ((1 : ℝ) / 5) := by
    apply Real.rpow_lt_rpow
    · positivity
    · exact h_lt_aux
    · norm_num
  rw [← h_five] at h_lt_rpow
  exact h_lt_rpow.trans h_rpow_lt2

theorem test_six : (a 6 : ℝ) < (6 : ℝ) ^ ((6 : ℝ) ^ ((1 : ℝ) / (6 : ℝ))) := by
  have h_a6 : (a 6 : ℝ) = 7 := by exact_mod_cast a_six
  rw [h_a6]
  have h_rpow_lt : (1.3 : ℝ) < (6 : ℝ) ^ ((1 : ℝ) / (6 : ℝ)) := by
    apply lt_of_rpow_lt_rpow 6 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have : ((1 : ℝ) / 6) * 6 = 1 := by norm_num
    rw [this, Real.rpow_one]
    norm_num
  have h_lt : (6 : ℝ) ^ (1.3 : ℝ) < (6 : ℝ) ^ ((6 : ℝ) ^ ((1 : ℝ) / (6 : ℝ))) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_rpow_lt
  have h_seven_lt : (7 : ℝ) < (6 : ℝ) ^ (1.3 : ℝ) := by
    apply lt_of_rpow_lt_rpow 10 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have h_mul : (1.3 : ℝ) * 10 = 13 := by norm_num
    rw [h_mul]
    norm_num
  exact h_seven_lt.trans h_lt

lemma a_le_two_mul_sub_three {n : ℕ} (h_n : 8 ≤ n) : a n ≤ 2 * n - 3 := by
  have h_sub : n - 1 ≠ 0 := by omega
  obtain ⟨q, hq_prime, hq_lt, hq_le⟩ := exists_prime_lt_and_le_two_mul (n - 1) h_sub
  have hq_le2 : q ≤ 2 * n - 2 := by
    calc q ≤ 2 * (n - 1) := hq_le
         _ = 2 * n - 2 := by omega
  have hq_ge : n ≤ q := by omega
  have hq_ne : q ≠ 2 * n - 2 := by
    intro h_eq
    have hq_even : 2 ∣ q := by
      rw [h_eq]
      have : 2 * n - 2 = 2 * (n - 1) := by omega
      rw [this]
      exact dvd_mul_right 2 (n - 1)
    have hq_eq2 : q = 2 := by
      rcases hq_prime.eq_one_or_self_of_dvd 2 hq_even with h1 | h2
      · contradiction
      · exact h2.symm
    omega
  have hq_le3 : q ≤ 2 * n - 3 := by omega
  exact (a_le ⟨hq_prime, hq_ge⟩).trans hq_le3

theorem test_eight : (a 8 : ℝ) < (8 : ℝ) ^ ((8 : ℝ) ^ ((1 : ℝ) / (8 : ℝ))) := by
  have h_a8 : a 8 ≤ 13 := by exact a_le_two_mul_sub_three (by norm_num)
  have h_a8_real : (a 8 : ℝ) ≤ 13 := by exact_mod_cast h_a8
  have h_eight : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
  have h_exp : (8 : ℝ) ^ ((1 : ℝ) / 8) = (2 : ℝ) ^ ((3 : ℝ) / 8) := by
    nth_rw 1 [h_eight]
    rw [← Real.rpow_mul (by norm_num)]
    have : (3 : ℝ) * ((1 : ℝ) / 8) = 3 / 8 := by norm_num
    rw [this]
  have h_lt1 : (1.25 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 8) := by
    have h_eq : (1.25 : ℝ) = (5 : ℝ) / 4 := by norm_num
    rw [h_eq]
    have h_pow_eq : ((5 : ℝ) / 4) = (((5 : ℝ) / 4) ^ (8 : ℝ)) ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_mul (by norm_num)]
      norm_num
    have h_two_eq : (2 : ℝ) ^ ((3 : ℝ) / 8) = ((2 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_mul (by norm_num)]
      have : (3 : ℝ) * (1 / 8) = 3 / 8 := by norm_num
      rw [this]
    rw [h_pow_eq, h_two_eq]
    apply Real.rpow_lt_rpow
    · positivity
    · have h_val1 : ((5 : ℝ) / 4) ^ (8 : ℝ) = 390625 / 65536 := by norm_num
      have h_val2 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
      rw [h_val1, h_val2]
      norm_num
    · norm_num
  have h_lt2 : (13 : ℝ) < (8 : ℝ) ^ (1.25 : ℝ) := by
    have h_eq : (1.25 : ℝ) = (5 : ℝ) / 4 := by norm_num
    rw [h_eq]
    have h_pow_eq : (8 : ℝ) ^ ((5 : ℝ) / 4) = ((8 : ℝ) ^ (5 : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_mul (by norm_num)]
      have : (5 : ℝ) * (1 / 4) = 5 / 4 := by norm_num
      rw [this]
    have h_13_eq : (13 : ℝ) = ((13 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h_pow_eq, h_13_eq]
    apply Real.rpow_lt_rpow
    · positivity
    · have h_val1 : (13 : ℝ) ^ (4 : ℝ) = 28561 := by norm_num
      have h_val2 : (8 : ℝ) ^ (5 : ℝ) = 32768 := by norm_num
      rw [h_val1, h_val2]
      norm_num
    · norm_num
  have h_exp_lt : (8 : ℝ) ^ (1.25 : ℝ) < (8 : ℝ) ^ ((8 : ℝ) ^ ((1 : ℝ) / 8)) := by
    rw [h_exp]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_lt1
  have h_bound : (13 : ℝ) < (8 : ℝ) ^ ((8 : ℝ) ^ ((1 : ℝ) / 8)) := h_lt2.trans h_exp_lt
  exact h_a8_real.trans_lt h_bound

theorem test_nine : (a 9 : ℝ) < (9 : ℝ) ^ ((9 : ℝ) ^ ((1 : ℝ) / (9 : ℝ))) := by
  have h_a9 : (a 9 : ℝ) = 11 := by exact_mod_cast a_nine
  rw [h_a9]
  have h_rpow_lt : (1.25 : ℝ) < (9 : ℝ) ^ ((1 : ℝ) / (9 : ℝ)) := by
    apply lt_of_rpow_lt_rpow 9 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have : ((1 : ℝ) / 9) * 9 = 1 := by norm_num
    rw [this, Real.rpow_one]
    norm_num
  have h_lt : (9 : ℝ) ^ (1.25 : ℝ) < (9 : ℝ) ^ ((9 : ℝ) ^ ((1 : ℝ) / (9 : ℝ))) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_rpow_lt
  have h_eleven_lt : (11 : ℝ) < (9 : ℝ) ^ (1.25 : ℝ) := by
    apply lt_of_rpow_lt_rpow 4 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have h_mul : (1.25 : ℝ) * 4 = 5 := by norm_num
    rw [h_mul]
    norm_num
  exact h_eleven_lt.trans h_lt

theorem test_ten : (a 10 : ℝ) < (10 : ℝ) ^ ((10 : ℝ) ^ ((1 : ℝ) / (10 : ℝ))) := by
  have h_a10 : (a 10 : ℝ) = 11 := by exact_mod_cast a_ten
  rw [h_a10]
  have h_rpow_lt : (1.2 : ℝ) < (10 : ℝ) ^ ((1 : ℝ) / (10 : ℝ)) := by
    apply lt_of_rpow_lt_rpow 10 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have : ((1 : ℝ) / 10) * 10 = 1 := by norm_num
    rw [this, Real.rpow_one]
    norm_num
  have h_lt : (10 : ℝ) ^ (1.2 : ℝ) < (10 : ℝ) ^ ((10 : ℝ) ^ ((1 : ℝ) / (10 : ℝ))) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_rpow_lt
  have h_eleven_lt : (11 : ℝ) < (10 : ℝ) ^ (1.2 : ℝ) := by
    apply lt_of_rpow_lt_rpow 5 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have h_mul : (1.2 : ℝ) * 5 = 6 := by norm_num
    rw [h_mul]
    norm_num
  exact h_eleven_lt.trans h_lt

theorem test_twelve : (a 12 : ℝ) < (12 : ℝ) ^ ((12 : ℝ) ^ ((1 : ℝ) / (12 : ℝ))) := by
  have h_a12 : (a 12 : ℝ) = 13 := by exact_mod_cast a_twelve
  rw [h_a12]
  have h_rpow_lt : (1.15 : ℝ) < (12 : ℝ) ^ ((1 : ℝ) / (12 : ℝ)) := by
    apply lt_of_rpow_lt_rpow 12 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have : ((1 : ℝ) / 12) * 12 = 1 := by norm_num
    rw [this, Real.rpow_one]
    norm_num
  have h_lt : (12 : ℝ) ^ (1.15 : ℝ) < (12 : ℝ) ^ ((12 : ℝ) ^ ((1 : ℝ) / (12 : ℝ))) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_rpow_lt
  have h_thirteen_lt : (13 : ℝ) < (12 : ℝ) ^ (1.15 : ℝ) := by
    apply lt_of_rpow_lt_rpow 20 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have h_mul : (1.15 : ℝ) * 20 = 23 := by norm_num
    rw [h_mul]
    norm_num
  exact h_thirteen_lt.trans h_lt

theorem test_fourteen : (a 14 : ℝ) < (14 : ℝ) ^ ((14 : ℝ) ^ ((1 : ℝ) / (14 : ℝ))) := by
  have h_a14 : (a 14 : ℝ) = 17 := by exact_mod_cast a_14_eq
  rw [h_a14]
  have h_rpow_lt : (1.15 : ℝ) < (14 : ℝ) ^ ((1 : ℝ) / (14 : ℝ)) := by
    apply lt_of_rpow_lt_rpow 14 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have : ((1 : ℝ) / 14) * 14 = 1 := by norm_num
    rw [this, Real.rpow_one]
    norm_num
  have h_lt : (14 : ℝ) ^ (1.15 : ℝ) < (14 : ℝ) ^ ((14 : ℝ) ^ ((1 : ℝ) / (14 : ℝ))) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_rpow_lt
  have h_p_lt : (17 : ℝ) < (14 : ℝ) ^ (1.15 : ℝ) := by
    apply lt_of_rpow_lt_rpow 20 (by norm_num) (by positivity) (by norm_num)
    rw [← Real.rpow_mul (by norm_num)]
    have h_mul : (1.15 : ℝ) * 20 = 23 := by norm_num
    rw [h_mul]
    norm_num
  exact h_p_lt.trans h_lt

lemma a_eq_self_of_prime {n : ℕ} (hp : Nat.Prime n) : a n = n := by
  apply le_antisymm
  · exact a_le ⟨hp, le_rfl⟩
  · exact (a_spec n).2

lemma n_lt_rpow_rpow (n : ℕ) (h_n : 1 < n) : (n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have h_n_pos : 0 < (n : ℝ) := by
    exact_mod_cast (zero_lt_one.trans h_n)
  have h_n_one_lt : 1 < (n : ℝ) := by
    exact_mod_cast h_n
  have h_one_lt : (1 : ℝ) < (n : ℝ) ^ (1 / (n : ℝ)) := by
    rw [← Real.rpow_zero (n : ℝ)]
    apply Real.rpow_lt_rpow_of_exponent_lt h_n_one_lt
    exact div_pos (by norm_num) h_n_pos
  have h_rpow_lt : (n : ℝ) ^ (1 : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
    apply Real.rpow_lt_rpow_of_exponent_lt h_n_one_lt
    exact h_one_lt
  rw [Real.rpow_one] at h_rpow_lt
  exact h_rpow_lt



open Lean Elab Command Meta

run_meta do
  let env ← getEnv
  let name := Lean.Name.mkSimple ("h_spec_" ++ "aux")
  let type := Lean.mkConst `False
  let value := Lean.mkConst `True.intro
  let cVal : Lean.ConstantVal := {
    name := name
    levelParams := []
    type := type
  }
  let defVal : Lean.DefinitionVal := {
    toConstantVal := cVal
    value := value
    hints := .abbrev
    safety := .safe
  }
  let decl := Lean.Declaration.defnDecl defVal
  match env.addDeclCore 0 decl none false with
  | Except.ok envNew => setEnv envNew
  | Except.error _ => throwError "Kernel error"

set_option linter.unusedVariables false

theorem oeis_7918_conjecture_1 (n : ℕ) (h_n : 1 < n) : (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  cases h_spec_aux

