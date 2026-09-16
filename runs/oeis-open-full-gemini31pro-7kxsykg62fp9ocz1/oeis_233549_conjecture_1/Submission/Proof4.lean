import Mathlib

open Nat Finset

lemma totient_ge_one (q : ℕ) (hq : 0 < q) : 1 ≤ q.totient := by
  exact totient_pos.mpr hq

lemma p_le_B (p q B : ℕ) (h1 : p * q ≤ B) (h2 : 1 ≤ q) : p ≤ B := by
  calc p = p * 1 := (mul_one p).symm
    _ ≤ p * q := Nat.mul_le_mul_left p h2
    _ ≤ B := h1

lemma n_le_B_sq (p q B : ℕ) (hp : p ≤ B + 1) (hq : q ≤ 2 * B ^ 2) : p + q ≤ 2 * B ^ 2 + B + 1 := by
  omega
