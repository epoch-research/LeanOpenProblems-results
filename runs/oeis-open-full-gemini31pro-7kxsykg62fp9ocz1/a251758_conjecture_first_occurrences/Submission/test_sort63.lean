import Mathlib

lemma a_pq_ge_16 (p q : ℕ) (hp : p ≥ 17) (hq : q ≥ 17) :
  let s := p + p * q + q * p * q
  (p * q)^2 / s ≥ 16 := by
  intro s
  have h1 : 16 * s ≤ (p * q)^2 := by
    calc
      16 * s = 16 * p + 16 * p * q + 16 * p * q^2 := by
        dsimp [s]
        ring
      _ = p * (16 + 16 * q + 16 * q^2) := by ring
      _ ≤ p * (q + 16 * q + 16 * q^2) := by
        apply Nat.mul_le_mul_left
        omega
      _ = p * (17 * q + 16 * q^2) := by ring
      _ ≤ p * (q * q + 16 * q^2) := by
        apply Nat.mul_le_mul_left
        nlinarith
      _ = p * (17 * q^2) := by ring
      _ ≤ p * (p * q^2) := by
        have : 17 * q^2 ≤ p * q^2 := Nat.mul_le_mul_right (q^2) hp
        exact Nat.mul_le_mul_left p this
      _ = (p * q)^2 := by ring
  have hs0 : s > 0 := by
    dsimp [s]
    omega
  exact (Nat.le_div_iff_mul_le hs0).mpr h1
