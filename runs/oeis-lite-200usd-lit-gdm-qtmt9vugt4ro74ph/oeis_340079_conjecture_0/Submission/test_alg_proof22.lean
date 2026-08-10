import Mathlib

lemma helper_ineq_contradiction (q r s : ℕ) (hq_ge : 5 ≤ q) (hr_ge : 7 ≤ r) (hs_ge : 11 ≤ s) (hq_lt_r : q < r) (hr_lt_s : r < s) :
    ¬ (2 * q - 1) * (2 * r - 1) * (2 * s - 1) < 6 * q * r * s := by
  have h1 : 11 * ((q : ℤ) * r) ≤ q * r * s := by
    calc 11 * ((q : ℤ) * r) ≤ (s : ℤ) * (q * r) := by
           have : (11 : ℤ) ≤ s := by omega
           have : (0 : ℤ) ≤ q * r := by positivity
           nlinarith
         _ = q * r * s := by ring
  have h2 : 7 * ((q : ℤ) * s) ≤ q * r * s := by
    calc 7 * ((q : ℤ) * s) ≤ (r : ℤ) * (q * s) := by
           have : (7 : ℤ) ≤ r := by omega
           have : (0 : ℤ) ≤ q * s := by positivity
           nlinarith
         _ = q * r * s := by ring
  have h3 : 5 * ((r : ℤ) * s) ≤ q * r * s := by
    calc 5 * ((r : ℤ) * s) ≤ (q : ℤ) * (r * s) := by
           have : (5 : ℤ) ≤ q := by omega
           have : (0 : ℤ) ≤ r * s := by positivity
           nlinarith
         _ = q * r * s := by ring
  zify [hq_ge, hr_ge, hs_ge, hq_lt_r, hr_lt_s]
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
  have h_expand : (2 * (q : ℤ) - 1) * (2 * r - 1) * (2 * s - 1) = 8 * ((q : ℤ) * r * s) - 4 * ((q : ℤ) * r) - 4 * ((q : ℤ) * s) - 4 * ((r : ℤ) * s) + 2 * (q : ℤ) + 2 * r + 2 * s - 1 := by ring
  rw [h_expand] at hc
  have hc_rew : 6 * (q : ℤ) * r * s = 6 * ((q : ℤ) * r * s) := by ring
  rw [hc_rew] at hc
  generalize h_qrs : (q : ℤ) * r * s = QRS at h1 h2 h3 hc
  generalize h_qr : (q : ℤ) * r = QR at h1 hc
  generalize h_qs : (q : ℤ) * s = QS at h2 hc
  generalize h_rs : (r : ℤ) * s = RS at h3 hc
  have h_bound : 2 * (q : ℤ) + 2 * r + 2 * s ≤ QRS := by
    calc 2 * (q : ℤ) + 2 * r + 2 * s ≤ 2 * s + 2 * s + 2 * s := by linarith
    _ = 6 * s := by ring
    _ ≤ QR * s := by
      have : (6 : ℤ) ≤ QR := by
        rw [← h_qr]
        have : (5 : ℤ) ≤ q := by linarith
        have : (7 : ℤ) ≤ r := by linarith
        nlinarith
      have : (0 : ℤ) ≤ s := by positivity
      nlinarith
    _ = QRS := by
      rw [← h_qrs, ← h_qr]
  linarith
