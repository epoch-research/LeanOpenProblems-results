import Mathlib

lemma test_algebra
    (p q r s : ℕ)
    (A B C : ℕ)
    (hA : A = 2 * p - 1)
    (hB : B = 2 * q - 1)
    (hC : C = 2 * r - 1)
    (Y' : ℕ)
    (Y : ℕ)
    (hY_eq : Y = (2 * s - 1) * Y')
    (k_s : ℕ)
    (g_s : ℕ)
    (h_q_g_s : q * g_s = 4 * A * B * Y' - k_s)
    (a_s : ℕ)
    (ha_s : A * B * C * Y' - 1 = s * a_s)
    (h_rk_eq : r * k_s = 2 * (A * B * Y') + a_s) :
    q * r * s * g_s = A * B * C * Y + 1 := by
  zify [h_q_g_s, h_rk_eq, ha_s, hY_eq]
  linear_combination
    (r * s : ℤ) * h_q_g_s - (s : ℤ) * h_rk_eq - ha_s - (A * B * C : ℤ) * hY_eq
