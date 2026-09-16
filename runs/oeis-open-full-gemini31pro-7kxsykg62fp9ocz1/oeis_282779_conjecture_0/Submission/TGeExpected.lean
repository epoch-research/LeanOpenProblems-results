import Mathlib
import Submission.ValidPeriod
import Submission.ValidPeriodN
import Submission.FinalDvd
import Submission.Divisibility
import Submission.SumIdent

open Nat Finset

lemma dvd_sub_of_mod_eq {a b n : ℕ} (h : a % n = b % n) : n ∣ a - b := by
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)

lemma T_ge_expected (p n T : ℕ) (hp : p.Prime) (hT_pos : T > 0)
  (hT_eq : ∀ k, (k + T)^p % n = k^p % n) :
  if p^2 ∣ n then n / p ≤ T else n ≤ T := by
  have h_zero_pow : 0^p = 0 := zero_pow hp.ne_zero
  have h_zero : T^p % n = 0 := by
    have h0 := hT_eq 0
    rw [zero_add, h_zero_pow, zero_mod] at h0
    exact h0
  have hdvd1 : n ∣ T^p := Nat.dvd_of_mod_eq_zero h_zero
  have h_one : (1 + T)^p % n = 1^p % n := hT_eq 1
  rw [one_pow] at h_one
  have hdvd2 : n ∣ (1 + T)^p - 1 := dvd_sub_of_mod_eq h_one
  rcases add_pow_ident p T hp with ⟨K, hK⟩
  rw [hK] at hdvd2
  have h_sub : 1 + p * T * (1 + T * K) + T^p - 1 = p * T * (1 + T * K) + T^p := by omega
  rw [h_sub] at hdvd2
  have h1 : n ∣ p * T * (1 + T * K) + T^p := hdvd2
  have hdvd3 : n ∣ p * T := my_divisibility n p T (1 + T * K) h1 hdvd1 (⟨K, rfl⟩)
  by_cases hp2 : p^2 ∣ n
  · rw [if_pos hp2]
    have hpn : p ∣ n := by
      have : p ∣ p^2 := by
        have : p^2 = p * p := by ring
        rw [this]
        exact dvd_mul_right p p
      exact dvd_trans this hp2
    have h_div : n / p ∣ T := by
      rcases hdvd3 with ⟨c, hc⟩
      have h_n : n = (n / p) * p := Nat.div_mul_cancel hpn |>.symm
      rw [h_n] at hc
      have h_cancel : T = n / p * c := by
        have h_mul : p * T = p * (n / p * c) := by
          rw [hc]
          ring
        exact mul_left_cancel₀ hp.ne_zero h_mul
      rw [h_cancel]
      exact dvd_mul_right (n / p) c
    exact Nat.le_of_dvd hT_pos h_div
  · rw [if_neg hp2]
    have h_dvd_final : n ∣ T := final_dvd n p T hp hdvd3 hdvd1 hp2
    exact Nat.le_of_dvd hT_pos h_dvd_final
