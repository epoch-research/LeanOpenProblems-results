import Mathlib

lemma test_gs_le_9
    (q r g_s_prime Y' a_s : ℕ)
    (hq_ge : 5 ≤ q)
    (hr_ge : 7 ≤ r)
    (hY'_pos : 1 ≤ Y')
    (ha_s_pos : 1 ≤ a_s)
    (h_prod : q * (r * (2 * g_s_prime)) = 2 * (2 * r - 1) * 3 * (2 * q - 1) * Y' - a_s) :
    g_s_prime ≤ 9 * Y' := by
  have h_prod_rew : 2 * q * r * g_s_prime = 6 * (2 * q - 1) * (2 * r - 1) * Y' - a_s := by
    calc 2 * q * r * g_s_prime = q * (r * (2 * g_s_prime)) := by ring
    _ = 2 * (2 * r - 1) * 3 * (2 * q - 1) * Y' - a_s := h_prod
    _ = 6 * (2 * q - 1) * (2 * r - 1) * Y' - a_s := by ring_nf
  have h_lt : 2 * q * r * g_s_prime < 6 * (2 * q - 1) * (2 * r - 1) * Y' := by
    rw [h_prod_rew]
    omega
  by_contra hc
  have hc_ge : g_s_prime ≥ 10 * Y' := by omega
  have h_mul_ge : 2 * q * r * g_s_prime ≥ 2 * q * r * (10 * Y') := Nat.mul_le_mul_left (2 * q * r) hc_ge
  have h_ring_LHS : 2 * q * r * (10 * Y') = 20 * q * r * Y' := by ring
  rw [h_ring_LHS] at h_mul_ge
  have h_ring_RHS : 6 * (2 * q - 1) * (2 * r - 1) * Y' = (12 * q * r - 6 * q - 6 * r + 3) * Y' := by
    -- we can prove this additively or using zify
    zify [hq_ge, hr_ge]
    ring
  -- wait, zify inside rw?
  -- let's write it as an equation on Nat using zify
  sorry
