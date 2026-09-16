import Mathlib
import Submission.Spec
import Submission.Proof22
import Submission.Proof23
import Submission.Proof24
import Submission.Proof25
import Submission.Proof20
import Submission.Proof19
import Submission.Proof6

open Nat BigOperators

lemma eq_two_pow_of_no_odd_prime_factor (n : ℕ) (hn0 : n > 0)
  (h_no_odd : ¬ ∃ q, q.Prime ∧ q > 2 ∧ q ∣ n) : ∃ m, n = 2 ^ m := by
  let k := padicValNat 2 n
  have h2 : 2 ^ k ∣ n := (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
  rcases h2 with ⟨c, hc⟩
  have hc_pos : c > 0 := by
    by_contra hc0
    have : c = 0 := by omega
    subst this
    have : n = 0 := by omega
    omega
  by_cases hc1 : c = 1
  · subst hc1
    use k
    rw [hc, mul_one]
  · have hc_neq_1 : c ≠ 1 := by omega
    have h_q : ∃ q, q.Prime ∧ q ∣ c := Nat.exists_prime_and_dvd hc_neq_1
    rcases h_q with ⟨q, hq_prime, hq_dvd⟩
    have hq_n : q ∣ n := by
      rw [hc]
      exact dvd_mul_of_dvd_right hq_dvd _
    by_cases hq2 : q = 2
    · subst hq2
      have h2_c : 2 ∣ c := hq_dvd
      rcases h2_c with ⟨d, hd⟩
      have hn_new : n = 2 ^ (k + 1) * d := by
        calc n = 2 ^ k * c := hc
          _ = 2 ^ k * (2 * d) := by rw [hd]
          _ = 2 ^ k * 2 * d := by ring
          _ = 2 ^ (k + 1) * d := by ring
      have h_dvd_n : 2 ^ (k + 1) ∣ n := ⟨d, hn_new⟩
      have hk_lt : k + 1 ≤ k := (padicValNat_dvd_iff_le (by omega)).mp h_dvd_n
      omega
    · have hq_gt2 : q > 2 := by
        have : q ≥ 2 := hq_prime.two_le
        omega
      have h_contra : ∃ q, q.Prime ∧ q > 2 ∧ q ∣ n := ⟨q, hq_prime, hq_gt2, hq_n⟩
      contradiction

lemma composite_contradiction (n : ℕ) (hn2 : n > 2) (hcomp : ¬ n.Prime)
  (h_dvd : n ∣ a (n - 1) + 2 ^ (n - 2)) : False := by
  have hc_neq_1 : n ≠ 1 := by omega
  have h_has_prime : ∃ p, p.Prime ∧ p ∣ n := Nat.exists_prime_and_dvd hc_neq_1
  rcases h_has_prime with ⟨p, hp_prime, hp_dvd⟩
  by_cases hodd : p > 2
  · exact odd_prime_factor_contradiction n p hn2 hcomp hp_prime hodd hp_dvd h_dvd
  · have hp_eq_2 : p = 2 := by
      have hp2 : p ≥ 2 := hp_prime.two_le
      omega
    subst hp_eq_2
    by_cases h_odd_prime : ∃ q, q.Prime ∧ q > 2 ∧ q ∣ n
    · rcases h_odd_prime with ⟨q, hq_prime, hq_odd, hq_dvd⟩
      exact odd_prime_factor_contradiction n q hn2 hcomp hq_prime hq_odd hq_dvd h_dvd
    · have h_pow2 : ∃ m, n = 2 ^ m := eq_two_pow_of_no_odd_prime_factor n (by omega) h_odd_prime
      rcases h_pow2 with ⟨m, hm_eq⟩
      exact power_of_two_contradiction n m hn2 hcomp hm_eq h_dvd
