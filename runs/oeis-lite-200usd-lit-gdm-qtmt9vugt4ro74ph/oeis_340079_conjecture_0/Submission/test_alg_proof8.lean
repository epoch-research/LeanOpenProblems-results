import Mathlib

lemma test_algebra_simple
    (q r s g_s c A B C Y : ℕ)
    (hC : C = 2 * r - 1)
    (hc_eq : c * r + 1 = A * B * Y)
    (h_eq_val : q * s * g_s = c * (2 * r - 1) + 2)
    (hr_pos : 1 ≤ 2 * r) :
    (r : ℤ) * (q * s * g_s) = (A : ℤ) * B * C * Y + 1 := by
  have hc_eq_int : (c : ℤ) * r + 1 = A * B * Y := by exact_mod_cast hc_eq
  have h_eq_val_int : (q : ℤ) * s * g_s = c * (2 * r - 1) + 2 := by
    zify [hr_pos] at h_eq_val
    exact h_eq_val
  have hC_int : (C : ℤ) = 2 * r - 1 := by
    zify [hr_pos] at hC
    exact hC
  linear_combination
    (r : ℤ) * h_eq_val_int + (2 * (r : ℤ) - 1) * hc_eq_int - (A * B * Y) * hC_int
