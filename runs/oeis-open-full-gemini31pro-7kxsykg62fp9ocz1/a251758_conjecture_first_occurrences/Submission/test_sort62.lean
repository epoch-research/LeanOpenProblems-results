import Mathlib

lemma a_pq_ge_16 (p q : ℕ) (hp : p ≥ 17) (hq : q ≥ 17) :
  let s := p + p * q + q * p * q
  (p * q)^2 / s ≥ 16 := by
  intro s
  have h1 : 16 * (p + p * q + q * p * q) ≤ (p * q)^2 := by
    calc
      16 * (p + p * q + q * p * q) = 16 * p * (1 + q + q^2) := by ring
      _ ≤ p * p * (1 + q + q^2) := by
        apply Nat.mul_le_mul_right
        nlinarith
      _ = p^2 + p^2 * q + p^2 * q^2 := by ring
      _ ≤ p^2 * q^2 := by
        -- wait, p^2 + p^2 * q + p^2 * q^2 is > p^2 * q^2 !
        sorry
  sorry
