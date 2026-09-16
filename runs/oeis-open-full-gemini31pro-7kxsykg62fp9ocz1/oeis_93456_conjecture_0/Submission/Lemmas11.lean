import Mathlib

open Nat

lemma Hn_gt1_proof (p : ℕ) (hp : 5 ≤ p) : 1 < p * (p - 2) := by
  have H1 : 3 ≤ p - 2 := by omega
  have H2 : 15 ≤ p * (p - 2) := Nat.mul_le_mul hp H1
  omega

lemma Hn_gtB_proof (p B : ℕ) (hp : 5 ≤ p) (hB : B < p) : B < p * (p - 2) := by
  have H1 : 3 ≤ p - 2 := by omega
  have H2 : p * 1 ≤ p * (p - 2) := Nat.mul_le_mul_left p (by omega)
  have H3 : p ≤ p * (p - 2) := by omega
  omega
