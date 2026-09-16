import Mathlib

lemma pqr_bound {p q r : ℤ} (h1 : 13 ≤ p) (h2 : p + 1 ≤ q) (h3 : q + 1 ≤ r)
  (h_eq : p * q * r = 1 + 2 * (p + q + r) + 4 * (p * q + q * r + p * r)) : False := by
  have h_factor : (p - 4) * (q - 4) * (r - 4) = 18 * p + 18 * q + 18 * r - 63 := by
    calc (p - 4) * (q - 4) * (r - 4) = p * q * r - 4 * (p * q + q * r + p * r) + 16 * (p + q + r) - 64 := by ring
      _ = (1 + 2 * (p + q + r) + 4 * (p * q + q * r + p * r)) - 4 * (p * q + q * r + p * r) + 16 * (p + q + r) - 64 := by rw [h_eq]
      _ = 18 * p + 18 * q + 18 * r - 63 := by ring
  have hp : 9 ≤ p - 4 := by omega
  have hq : 10 ≤ q - 4 := by omega
  have hr : 11 ≤ r - 4 := by omega
  have h_bound1 : 9 * (q - 4) * (r - 4) ≤ (p - 4) * (q - 4) * (r - 4) := by nlinarith
  have h_bound2 : 9 * 10 * (r - 4) ≤ 9 * (q - 4) * (r - 4) := by nlinarith
  nlinarith
