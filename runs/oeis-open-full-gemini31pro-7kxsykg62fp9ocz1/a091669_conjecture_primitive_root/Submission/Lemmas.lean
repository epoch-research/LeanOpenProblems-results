import Mathlib

open Nat BigOperators

lemma two_pow_sub_one_odd (k : ℕ) (hk : 1 ≤ k) : ¬ 2 ∣ 2^k - 1 := by
  intro h
  have : (2^k - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
  have h_pow : 2^k ≥ 2 := by
    have : 2^k ≥ 2^1 := Nat.pow_le_pow_right (by decide : 2 > 0) hk
    exact this
  have : (2^k - 1) % 2 = 1 := by
    have : 2^k % 2 = 0 := by
      rcases k with _ | k'
      · contradiction
      · rw [Nat.pow_succ]
        omega
    omega
  omega

lemma prod_odd_is_odd (n : ℕ) : ¬ 2 ∣ ∏ k ∈ Finset.Ico 1 n, (2^k - 1) := by
  induction' n with n ih
  · simp
  · by_cases hn : n = 0
    · subst hn; simp
    · rw [Finset.prod_Ico_succ_top (by omega)]
      intro h
      have : 2 ∣ ∏ k ∈ Finset.Ico 1 n, (2^k - 1) ∨ 2 ∣ 2^n - 1 := (Nat.Prime.dvd_mul Nat.prime_two).mp h
      rcases this with h1 | h2
      · exact ih h1
      · exact two_pow_sub_one_odd n (by omega) h2
lemma padicValNat_two_prod (n : ℕ) : padicValNat 2 (∏ k ∈ Finset.Ico 1 n, (2^k - 1)) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  exact prod_odd_is_odd n
