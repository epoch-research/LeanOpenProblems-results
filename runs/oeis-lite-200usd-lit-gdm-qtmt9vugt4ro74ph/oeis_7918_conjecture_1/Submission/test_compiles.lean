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

theorem test_four : (a 4 : ℝ) < (4 : ℝ) ^ ((4 : ℝ) ^ ((1 : ℝ) / (4 : ℝ))) := by
  have h_a4 : (a 4 : ℝ) = 5 := by
    exact_mod_cast a_four
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
  have h_five_val : (5 : ℝ) ^ (5 : ℝ) = 3125 := by
    norm_num
  have h_four_val : (4 : ℝ) ^ (7 : ℝ) = 16384 := by
    norm_num
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
  have h_a8 : a 8 ≤ 13 := by
    exact a_le_two_mul_sub_three (by norm_num)
  have h_a8_real : (a 8 : ℝ) ≤ 13 := by
    exact_mod_cast h_a8
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
