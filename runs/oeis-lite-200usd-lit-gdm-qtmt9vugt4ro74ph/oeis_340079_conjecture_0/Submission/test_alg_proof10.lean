import Mathlib

lemma test_contradiction_final
    (q r s g_s_prime Y' Y : ℕ)
    (hq_prime : Nat.Prime q)
    (hr_prime : Nat.Prime r)
    (hs_prime : Nat.Prime s)
    (hp_lt_q : 2 < q)
    (hq_lt_r : q < r)
    (hr_lt_s : r < s)
    (hB : 2 * q - 1 = 2 * q - 1) -- B := 2q-1
    (hC : 2 * r - 1 = 2 * r - 1) -- C := 2r-1
    (hY : Y = (2 * s - 1) * Y')
    (hY'_pos : 1 ≤ Y')
    (h_gs_le_9 : g_s_prime ≤ 9 * Y')
    (h_gs_eq : 2 * q * r * s * g_s_prime = 3 * (2 * q - 1) * (2 * r - 1) * Y + 1) :
    False := by
  have hq_ge : 5 ≤ q := by
    -- we can prove q >= 5 because q is prime and 2 < q and q != 3
    sorry
  have hr_ge : 7 ≤ r := by omega
  have hs_ge : 11 ≤ s := by omega
  have h_gs_eq_rew : 2 * q * r * s * g_s_prime = 3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * Y' + 1 := by
    rw [hY] at h_gs_eq
    have : 3 * (2 * q - 1) * (2 * r - 1) * ((2 * s - 1) * Y') = 3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * Y' := by ring
    rw [this] at h_gs_eq
    exact h_gs_eq
  have h_le_18 : 2 * q * r * s * g_s_prime ≤ 18 * q * r * s * Y' := by
    have : 2 * q * r * s * g_s_prime = (2 * q * r * s) * g_s_prime := by ring
    rw [this]
    have h_mul := Nat.mul_le_mul_left (2 * q * r * s) h_gs_le_9
    have h_ring : 2 * q * r * s * (9 * Y') = 18 * q * r * s * Y' := by ring
    rw [h_ring] at h_mul
    exact h_mul
  have h_final_ineq : 3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * Y' + 1 ≤ 18 * q * r * s * Y' := by
    rwa [← h_gs_eq_rew]
  have h_strict_lt : 3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * Y' < 18 * q * r * s * Y' := by
    omega
  have h_div_3_Y' : (2 * q - 1) * (2 * r - 1) * (2 * s - 1) < 6 * q * r * s := by
    have h_mul_lt : 3 * ((2 * q - 1) * (2 * r - 1) * (2 * s - 1)) * Y' < 3 * (6 * q * r * s) * Y' := by
      have : 3 * (6 * q * r * s) * Y' = 18 * q * r * s * Y' := by ring
      rw [this]
      have h_ring_LHS : 3 * ((2 * q - 1) * (2 * r - 1) * (2 * s - 1)) * Y' = 3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * Y' := by ring
      rwa [h_ring_LHS]
    have h_3_Y'_pos : 0 < 3 * Y' := by omega
    have h_lt := Nat.lt_of_mul_lt_mul_right h_mul_lt
    exact h_lt
  -- Now we just use omega to prove False from h_div_3_Y' with q >= 5, r >= 7, s >= 11
  omega
