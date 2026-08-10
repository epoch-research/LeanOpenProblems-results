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
  have h_q_g_s_int : (q : ℤ) * g_s = 4 * A * B * Y' - k_s := by zify; linarith [h_q_g_s]
  have h_rk_eq_int : (r : ℤ) * k_s = 2 * (A * B * Y') + a_s := by zify; linarith [h_rk_eq]
  have ha_s_int : (A : ℤ) * B * C * Y' - 1 = s * a_s := by zify; linarith [ha_s]
  have hY_eq_int : (Y : ℤ) = (2 * s - 1) * Y' := by zify; linarith [hY_eq]
  zify
  linear_combination
    ((r : ℤ) * s) * h_q_g_s_int - (s : ℤ) * h_rk_eq_int - ha_s_int - ((A : ℤ) * B * C) * hY_eq_int
