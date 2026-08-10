import Mathlib

open Nat

lemma dvd_term_of_not_dvd (p k n : ℕ) [hp : Fact (Nat.Prime p)] (hk_le : k ≤ n) (hk_nz : k ≠ 0) (hk : ¬ p ∣ k) :
  p ^ (padicValNat p n.factorial) ∣ n.factorial / k := by
  have h_div : k ∣ n.factorial := Nat.dvd_factorial (by omega) hk_le
  have h_val : padicValNat p (n.factorial / k) = padicValNat p n.factorial := by
    rw [padicValNat.div_of_dvd h_div]
    have : padicValNat p k = 0 := padicValNat.eq_zero_of_not_dvd hk
    omega
  rw [← h_val]
  exact pow_padicValNat_dvd
