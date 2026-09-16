import Mathlib

lemma a_pq (p q : ℕ) (hp : p ≥ 17) (hq : q ≥ 19) :
  p * q * q ≥ 15 * (1 + q + q * q) := by
  calc
    p * q * q ≥ 17 * (q * q) := by nlinarith
    _ = 2 * (q * q) + 15 * (q * q) := by ring
    _ ≥ 2 * (19 * q) + 15 * (q * q) := by nlinarith
    _ = 38 * q + 15 * (q * q) := by ring
    _ = 15 * q + 23 * q + 15 * (q * q) := by ring
    _ ≥ 15 * q + 23 * 19 + 15 * (q * q) := by nlinarith
    _ = 15 + 422 + 15 * q + 15 * (q * q) := by ring
    _ ≥ 15 * 1 + 15 * q + 15 * (q * q) := by nlinarith
    _ = 15 * (1 + q + q * q) := by ring
