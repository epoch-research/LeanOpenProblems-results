import FormalConjectures.Util.ProblemImports

open Nat Real

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

lemma a_spec (n : ℕ) : Nat.Prime (a n) ∧ n ≤ a n := by
  unfold a
  exact @Nat.find_spec (fun p : ℕ => Nat.Prime p ∧ n ≤ p) _ _

lemma a_eq_iff (n m : ℕ) : a n = m ↔ (Nat.Prime m ∧ n ≤ m) ∧ (∀ k < m, ¬ (Nat.Prime k ∧ n ≤ k)) := by
  unfold a
  exact Nat.find_eq_iff _

lemma a_eq_self_of_prime (n : ℕ) (hn : Nat.Prime n) : a n = n := by
  rw [a_eq_iff]
  refine ⟨⟨hn, le_refl _⟩, fun m hm => by
    rintro ⟨h_prime, h_le⟩
    omega
  ⟩

lemma helper (n : ℕ) (hn : 1 < n) : (n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have hn_real : 1 < (n : ℝ) := by exact_mod_cast hn
  have h_lt : (1 : ℝ) < (n : ℝ) ^ (1 / (n : ℝ)) := by
    have h_div_pos : 0 < 1 / (n : ℝ) := by positivity
    have h_base_lt : (1 : ℝ) ^ (1 / (n : ℝ)) < (n : ℝ) ^ (1 / (n : ℝ)) := by
      exact Real.rpow_lt_rpow zero_le_one hn_real h_div_pos
    rw [Real.one_rpow] at h_base_lt
    exact h_base_lt
  have h_rpow_lt := Real.rpow_lt_rpow_of_exponent_lt hn_real h_lt
  rw [Real.rpow_one] at h_rpow_lt
  exact h_rpow_lt

theorem prime_case (n : ℕ) (hn : Nat.Prime n) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have ha : a n = n := a_eq_self_of_prime n hn
  rw [ha]
  exact helper n h_n

lemma lt_four_rpow : (7 / 5 : ℝ) < (4 : ℝ) ^ (1 / 4 : ℝ) := by
  have h1 : (7 / 5 : ℝ) ^ (4 : ℝ) < 4 := by norm_num
  have h3 := Real.rpow_lt_rpow (by positivity) h1 (by positivity : 0 < (1 / 4 : ℝ))
  rw [← Real.rpow_mul (by positivity)] at h3
  norm_num at h3
  exact h3

lemma lt_four_rpow_step2 : (5 : ℝ) < (4 : ℝ) ^ ((4 : ℝ) ^ (1 / 4 : ℝ)) := by
  have h_base : (1 : ℝ) < 4 := by norm_num
  have h_exp := lt_four_rpow
  have h4 := Real.rpow_lt_rpow_of_exponent_lt h_base h_exp
  have h5 : (5 : ℝ) < (4 : ℝ) ^ (7 / 5 : ℝ) := by
    have h6 : (5 : ℝ) ^ (5 : ℝ) < (4 : ℝ) ^ (7 : ℝ) := by norm_num
    have h7 : (5 : ℝ) ^ (5 : ℝ) < ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (5 : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      have h_eq : (7 / 5 : ℝ) * 5 = 7 := by norm_num
      rw [h_eq]
      exact h6
    have h9 := Real.rpow_lt_rpow (by positivity) h7 (by positivity : 0 < (1 / 5 : ℝ))
    rw [← Real.rpow_mul (by positivity)] at h9
    rw [← Real.rpow_mul (by positivity)] at h9
    norm_num at h9
    exact h9
  exact lt_trans h5 h4

lemma lt_six_rpow : (13 / 10 : ℝ) < (6 : ℝ) ^ (1 / 6 : ℝ) := by
  have h1 : (13 / 10 : ℝ) ^ (6 : ℝ) < 6 := by norm_num
  have h3 := Real.rpow_lt_rpow (by positivity) h1 (by positivity : 0 < (1 / 6 : ℝ))
  rw [← Real.rpow_mul (by positivity)] at h3
  norm_num at h3
  exact h3

lemma lt_six_rpow_step2 : (7 : ℝ) < (6 : ℝ) ^ ((6 : ℝ) ^ (1 / 6 : ℝ)) := by
  have h_base : (1 : ℝ) < 6 := by norm_num
  have h_exp := lt_six_rpow
  have h4 := Real.rpow_lt_rpow_of_exponent_lt h_base h_exp
  have h5 : (7 : ℝ) < (6 : ℝ) ^ (13 / 10 : ℝ) := by
    have h6 : (7 : ℝ) ^ (10 : ℝ) < (6 : ℝ) ^ (13 : ℝ) := by norm_num
    have h7 : (7 : ℝ) ^ (10 : ℝ) < ((6 : ℝ) ^ (13 / 10 : ℝ)) ^ (10 : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      have h_eq : (13 / 10 : ℝ) * 10 = 13 := by norm_num
      rw [h_eq]
      exact h6
    have h9 := Real.rpow_lt_rpow (by positivity) h7 (by positivity : 0 < (1 / 10 : ℝ))
    rw [← Real.rpow_mul (by positivity)] at h9
    rw [← Real.rpow_mul (by positivity)] at h9
    norm_num at h9
    exact h9
  exact lt_trans h5 h4

theorem oeis_7918_conjecture_1 (n : ℕ) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  by_cases hn : Nat.Prime n
  · exact prime_case n hn h_n
  · rcases le_or_gt 8 n with h | h
    · sorry
    · interval_cases n
      · have h1 : a 4 = 5 := by
          rw [a_eq_iff]
          refine ⟨⟨by norm_num, by omega⟩, fun k hk => ?_⟩
          interval_cases k
          · rintro ⟨-, h_ge⟩; omega
          · rintro ⟨-, h_ge⟩; omega
          · rintro ⟨h_prime, _⟩; contradiction
          · rintro ⟨-, h_ge⟩; omega
        rw [h1]
        exact lt_four_rpow_step2
      · have h1 : a 6 = 7 := by
          rw [a_eq_iff]
          refine ⟨⟨by norm_num, by omega⟩, fun k hk => ?_⟩
          interval_cases k
          · rintro ⟨-, h_ge⟩; omega
          · rintro ⟨-, h_ge⟩; omega
          · rintro ⟨h_prime, _⟩; contradiction
          · rintro ⟨-, h_ge⟩; omega
          · rintro ⟨h_prime, _⟩; contradiction
          · rintro ⟨h_prime, _⟩; contradiction
        rw [h1]
        exact lt_six_rpow_step2
