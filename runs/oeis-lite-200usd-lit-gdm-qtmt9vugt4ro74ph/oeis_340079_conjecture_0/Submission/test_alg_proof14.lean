import Mathlib

lemma helper_ineq_contradiction (q r s : ℕ) (hq_ge : 5 ≤ q) (hr_ge : 7 ≤ r) (hs_ge : 11 ≤ s) :
    ¬ (2 * q - 1) * (2 * r - 1) * (2 * s - 1) < 6 * q * r * s := by
  have h1 : 4 * ((q : ℤ) * r) ≤ q * r * s := by
    calc 4 * ((q : ℤ) * r) ≤ (s : ℤ) * (q * r) := by
           have : (4 : ℤ) ≤ s := by omega
           have : (0 : ℤ) ≤ q * r := by positivity
           nlinarith
         _ = q * r * s := by ring
  have h2 : 4 * ((q : ℤ) * s) ≤ q * r * s := by
    calc 4 * ((q : ℤ) * s) ≤ (r : ℤ) * (q * s) := by
           have : (4 : ℤ) ≤ r := by omega
           have : (0 : ℤ) ≤ q * s := by positivity
           nlinarith
         _ = q * r * s := by ring
  have h3 : 4 * ((r : ℤ) * s) ≤ q * r * s := by
    calc 4 * ((r : ℤ) * s) ≤ (q : ℤ) * (r * s) := by
           have : (4 : ℤ) ≤ q := by omega
           have : (0 : ℤ) ≤ r * s := by positivity
           nlinarith
         _ = q * r * s := by ring
  zify [hq_ge, hr_ge, hs_ge]
  have h_q_cast : ((2 * q - 1 : ℕ) : ℤ) = 2 * (q : ℤ) - 1 := by
    have : 1 ≤ 2 * q := by omega
    exact Nat.cast_sub this
  have h_r_cast : ((2 * r - 1 : ℕ) : ℤ) = 2 * (r : ℤ) - 1 := by
    have : 1 ≤ 2 * r := by omega
    exact Nat.cast_sub this
  have h_s_cast : ((2 * s - 1 : ℕ) : ℤ) = 2 * (s : ℤ) - 1 := by
    have : 1 ≤ 2 * s := by omega
    exact Nat.cast_sub this
  intro hc
  rw [h_q_cast, h_r_cast, h_s_cast] at hc
  have h_expand : (2 * (q : ℤ) - 1) * (2 * r - 1) * (2 * s - 1) = 8 * q * r * s - 4 * q * r - 4 * q * s - 4 * r * s + 2 * q + 2 * r + 2 * s - 1 := by ring
  rw [h_expand] at hc
  linarith
