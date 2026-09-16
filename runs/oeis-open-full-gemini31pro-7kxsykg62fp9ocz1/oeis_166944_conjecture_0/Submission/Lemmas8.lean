import Submission.Lemmas7
import Mathlib

lemma gcd_odd_is_odd (a b : ℕ) (ha : a % 2 = 1) : Nat.gcd a b % 2 = 1 := by
  by_contra h
  have h_even : Nat.gcd a b % 2 = 0 := by omega
  have : 2 ∣ Nat.gcd a b := by omega
  have : 2 ∣ a := Nat.dvd_trans this (Nat.gcd_dvd_left a b)
  have : a % 2 = 0 := by omega
  omega

lemma gcd_odd_is_odd2 (a b : ℕ) (hb : b % 2 = 1) : Nat.gcd a b % 2 = 1 := by
  rw [Nat.gcd_comm]
  exact gcd_odd_is_odd b a hb

lemma C_even (n : ℕ) (hn : 2 ≤ n) : C n % 2 = 0 := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hC : C (k + 1) = C k + d (k + 1) - 1 := C_add_d k (by omega)
    rw [hC]
    have hd : d (k + 1) =
      if (k + 1) % 2 = 0 then
        Nat.gcd (k + 1) (C k - 1)
      else
        Nat.gcd (k - 1) (C k + 1) := d_val2 (k + 1) (by omega)
    rw [hd]
    split_ifs with h_even
    · have h_C_odd : (C k - 1) % 2 = 1 := by
        have : 1 ≤ C k := C_ge_one k (by omega)
        omega
      have h_gcd_odd : Nat.gcd (k + 1) (C k - 1) % 2 = 1 := gcd_odd_is_odd2 _ _ h_C_odd
      omega
    · have h_C_odd : (C k + 1) % 2 = 1 := by omega
      have h_gcd_odd : Nat.gcd (k - 1) (C k + 1) % 2 = 1 := gcd_odd_is_odd2 _ _ h_C_odd
      omega
