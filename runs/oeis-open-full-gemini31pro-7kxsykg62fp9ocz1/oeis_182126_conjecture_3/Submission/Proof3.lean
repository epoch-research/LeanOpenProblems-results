import Mathlib

open Nat

lemma mod_eq (p0 p1 p2 : ℕ) (h1 : p0 ≤ p1) (h2 : p1 ≤ p2) :
  (p0 * p1) % p2 = ((p2 - p1) * (p2 - p0)) % p2 := by
  have H : (p2 - p1) * (p2 - p0) + (p1 + p0) * p2 = p2 * p2 + p0 * p1 := by
    zify [h1, h2, le_trans h1 h2]
    ring
  have H2 : ((p2 - p1) * (p2 - p0) + (p1 + p0) * p2) % p2 = (p2 * p2 + p0 * p1) % p2 := by
    rw [H]
  rw [Nat.add_mul_mod_self_right] at H2
  have H3 : (p2 * p2 + p0 * p1) % p2 = (p0 * p1 + p2 * p2) % p2 := by rw [add_comm]
  rw [H3] at H2
  have H4 : (p0 * p1 + p2 * p2) % p2 = (p0 * p1 + p2 * p2) % p2 := rfl
  rw [Nat.add_mul_mod_self_right] at H2
  exact H2.symm
