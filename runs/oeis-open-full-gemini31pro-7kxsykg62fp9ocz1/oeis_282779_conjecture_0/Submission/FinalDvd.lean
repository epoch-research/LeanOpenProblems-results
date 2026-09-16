import Mathlib

open Nat

lemma final_dvd (n p T : ℕ) (hp : p.Prime) (h1 : n ∣ p * T) (h2 : n ∣ T^p) (h3 : ¬ p^2 ∣ n) :
  n ∣ T := by
  by_cases hpn : p ∣ n
  · have hcop : Coprime (n / p) p := by
      apply Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have : p * p ∣ n := Nat.mul_dvd_of_dvd_div hpn h
      rw [← pow_two] at this
      exact h3 this
    have h1' : n / p ∣ T := by
      have : n / p * p ∣ T * p := by
        rw [Nat.div_mul_cancel hpn, mul_comm T p]
        exact h1
      exact Nat.dvd_of_mul_dvd_mul_right hp.pos this
    have hpT : p ∣ T := Nat.Prime.dvd_of_dvd_pow hp (Nat.dvd_trans hpn h2)
    have : n / p * p ∣ T := hcop.mul_dvd_of_dvd_of_dvd h1' hpT
    rwa [Nat.div_mul_cancel hpn] at this
  · have hcop : Coprime n p := Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)
    exact hcop.dvd_of_dvd_mul_left h1
