import Mathlib

lemma test_ineq
    (q r s : ℕ)
    (hq_ge : 5 ≤ q)
    (hr_ge : 7 ≤ r)
    (hs_ge : 11 ≤ s) :
    ¬ (2 * q - 1) * (2 * r - 1) * (2 * s - 1) < 6 * q * r * s := by
  have h1 : 4 * (q * r) ≤ s * (q * r) := Nat.mul_le_mul_right (q * r) (by omega)
  have h1_ring : s * (q * r) = q * r * s := by ring
  rw [h1_ring] at h1
  have h2 : 4 * (q * s) ≤ r * (q * s) := Nat.mul_le_mul_right (q * s) (by omega)
  have h2_ring : r * (q * s) = q * r * s := by ring
  rw [h2_ring] at h2
  have h3 : 4 * (r * s) ≤ q * (r * s) := Nat.mul_le_mul_right (r * s) (by omega)
  have h3_ring : q * (r * s) = q * r * s := by ring
  rw [h3_ring] at h3
  
  -- Expanding the LHS
  have h_LHS : (2 * q - 1) * (2 * r - 1) * (2 * s - 1) = 8 * q * r * s - 4 * q * r - 4 * q * s - 4 * r * s + 2 * q + 2 * r + 2 * s - 1 := by
    -- we can prove this expanding LHS
    have h_sub_q : 2 * q - 1 ≤ 2 * q := by omega
    have h_sub_r : 2 * r - 1 ≤ 2 * r := by omega
    have h_sub_s : 2 * s - 1 ≤ 2 * s := by omega
    -- Actually we can just prove it using zify and ring
    zify [hq_ge, hr_ge, hs_ge]
    ring
  rw [h_LHS]
  intro hc
  zify [hq_ge, hr_ge, hs_ge] at hc h1 h2 h3
  linarith
