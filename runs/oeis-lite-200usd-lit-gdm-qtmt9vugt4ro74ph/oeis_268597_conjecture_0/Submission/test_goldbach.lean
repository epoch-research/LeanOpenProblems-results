import Mathlib

open Nat

lemma totient_goldbach_solution (d p : ℕ) (hd : d.Prime) (hp : p.Prime) (h_diff : d ≠ p) (hd_gt : d ≥ 3) (hp_gt : p ≥ 3) :
  (d * p - 1) % ((d - 1) * (p - 1)) = d + p - 2 := by
  have hd2 : 2 ≤ d := hd.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : d * p - 1 = (d - 1) * (p - 1) + (d + p - 2) := by
    have h_mul : (d - 1) * (p - 1) = d * p - d - p + 1 := by
      omega
    omega
  rw [h1]
  have h5 : d + p - 2 < (d - 1) * (p - 1) := by
    -- We want to show d + p - 2 < (d-1)*(p-1) = d*p - d - p + 1
    -- which is 2*d + 2*p - 3 < d*p
    -- since d >= 3 and p >= 3, let d = 3 + x, p = 3 + y
    have hd3 : 3 ≤ d := hd_gt
    have hp3 : 3 ≤ p := hp_gt
    nlinarith
  rw [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt h5
