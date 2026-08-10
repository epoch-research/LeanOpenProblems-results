import Mathlib

lemma test_c_nonzero
    (p q r s : ℕ)
    (C : ℕ)
    (g_s : ℕ)
    (c : ℕ)
    (hp_prime : Nat.Prime p)
    (hp_lt_q : p < q)
    (hq_lt_r : q < r)
    (hr_lt_s : r < s)
    (h_C : C = 2 * r - 1)
    (h_alg_s : c * C + 2 = q * s * g_s) :
    c ≠ 0 := by
  intro hc_zero
  subst hc_zero
  have hp_ge2 : 2 ≤ p := hp_prime.two_le
  have hq_ge3 : 3 ≤ q := by omega
  have hs_ge5 : 5 ≤ s := by omega
  rw [zero_mul, zero_add] at h_alg_s
  by_cases hg0 : g_s = 0
  · subst hg0
    omega
  · have hg_ge1 : 1 ≤ g_s := by omega
    have h_mul_ge : 15 * 1 ≤ q * s * g_s := Nat.mul_le_mul (Nat.mul_le_mul hq_ge3 hs_ge5) hg_ge1
    omega








