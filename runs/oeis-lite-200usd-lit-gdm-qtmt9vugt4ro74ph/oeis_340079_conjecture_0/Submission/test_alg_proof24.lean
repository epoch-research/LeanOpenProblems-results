import FormalConjectures.Util.ProblemImports

lemma helper_ineq_contradiction (q r s : ℤ) (hq_ge : 5 ≤ q) (hr_ge : 7 ≤ r) (hs_ge : 11 ≤ s) (hq_lt_r : q < r) (hr_lt_s : r < s) :
    ¬ (2 * q - 1) * (2 * r - 1) * (2 * s - 1) < 6 * q * r * s := by
  have h1 : 11 * (q * r) ≤ q * r * s := by
    calc 11 * (q * r) ≤ s * (q * r) := by
           have : (11 : ℤ) ≤ s := hs_ge
           have : (0 : ℤ) ≤ q * r := by positivity
           nlinarith
         _ = q * r * s := by ring
  have h2 : 7 * (q * s) ≤ q * r * s := by
    calc 7 * (q * s) ≤ r * (q * s) := by
           have : (7 : ℤ) ≤ r := hr_ge
           have : (0 : ℤ) ≤ q * s := by positivity
           nlinarith
         _ = q * r * s := by ring
  have h3 : 5 * (r * s) ≤ q * r * s := by
    calc 5 * (r * s) ≤ q * (r * s) := by
           have : (5 : ℤ) ≤ q := hq_ge
           have : (0 : ℤ) ≤ r * s := by positivity
           nlinarith
         _ = q * r * s := by ring
  intro hc
  have h_expand : (2 * q - 1) * (2 * r - 1) * (2 * s - 1) = 8 * (q * r * s) - 4 * (q * r) - 4 * (q * s) - 4 * (r * s) + 2 * q + 2 * r + 2 * s - 1 := by ring
  rw [h_expand] at hc
  generalize h_qrs : q * r * s = QRS at h1 h2 h3 hc
  generalize h_qr : q * r = QR at h1 hc
  generalize h_qs : q * s = QS at h2 hc
  generalize h_rs : r * s = RS at h3 hc
  have h_bound : 2 * q + 2 * r + 2 * s ≤ QRS := by
    calc 2 * q + 2 * r + 2 * s ≤ 2 * s + 2 * s + 2 * s := by linarith
    _ = 6 * s := by ring
    _ ≤ QR * s := by
      have : (6 : ℤ) ≤ QR := by
        rw [← h_qr]
        nlinarith
      have : (0 : ℤ) ≤ s := by positivity
      nlinarith
    _ = QRS := by
      rw [← h_qrs, ← h_qr]
  linarith

lemma helper_ineq_contradiction_q3 (r s : ℤ) (hr_ge : 5 ≤ r) (hs_ge : 7 ≤ s) (hr_lt_s : r < s) :
    ¬ 5 * (2 * r - 1) * (2 * s - 1) < 18 * r * s := by
  have h1 : 7 * r ≤ r * s := by
    have : (7 : ℤ) ≤ s := hs_ge
    have : (0 : ℤ) ≤ r := by positivity
    nlinarith
  have h2 : 5 * s ≤ r * s := by
    have : (5 : ℤ) ≤ r := hr_ge
    have : (0 : ℤ) ≤ s := by positivity
    nlinarith
  intro hc
  have h_expand : 5 * (2 * r - 1) * (2 * s - 1) = 20 * (r * s) - 10 * r - 10 * s + 5 := by ring
  rw [h_expand] at hc
  generalize h_rs : r * s = RS at h1 h2 hc
  linarith

lemma test_contradiction_final
    (q r s g_s_prime Y' Y : ℕ)
    (hq_prime : Nat.Prime q)
    (hr_prime : Nat.Prime r)
    (hs_prime : Nat.Prime s)
    (hp_lt_q : 2 < q)
    (hq_lt_r : q < r)
    (hr_lt_s : r < s)
    (hY : Y = (2 * s - 1) * Y')
    (hY'_pos : 1 ≤ Y')
    (h_gs_le_9 : g_s_prime ≤ 9 * Y')
    (h_gs_eq : 2 * q * r * s * g_s_prime = 3 * (2 * q - 1) * (2 * r - 1) * Y + 1) :
    False := by
  have hq_ge3 : 3 ≤ q := by
    have : q ≠ 0 := by omega
    have : q ≠ 2 := by
      intro hc
      rw [hc] at hp_lt_q
      revert hp_lt_q; decide
    have : q ≠ 1 := hq_prime.ne_one
    omega
  by_cases hq5 : q ≥ 5
  · have hr_ge : 7 ≤ r := by
      have : q < r := hq_lt_r
      have : r ≠ 6 := by
        intro hc
        rw [hc] at hr_prime
        revert hr_prime; decide
      omega
    have hs_ge : 11 ≤ s := by
      have : r < s := hr_lt_s
      have : s ≠ 8 := by intro hc; rw [hc] at hs_prime; revert hs_prime; decide
      have : s ≠ 9 := by intro hc; rw [hc] at hs_prime; revert hs_prime; decide
      have : s ≠ 10 := by intro hc; rw [hc] at hs_prime; revert hs_prime; decide
      omega
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
    have hq_ge_int : (5 : ℤ) ≤ (q : ℤ) := by zify; exact hq5
    have hr_ge_int : (7 : ℤ) ≤ (r : ℤ) := by zify; exact hr_ge
    have hs_ge_int : (11 : ℤ) ≤ (s : ℤ) := by zify; exact hs_ge
    have hq_lt_r_int : (q : ℤ) < (r : ℤ) := by zify; exact hq_lt_r
    have hr_lt_s_int : (r : ℤ) < (s : ℤ) := by zify; exact hr_lt_s
    have h_div_3_Y'_int : (2 * (q : ℤ) - 1) * (2 * (r : ℤ) - 1) * (2 * (s : ℤ) - 1) < 6 * (q : ℤ) * (r : ℤ) * (s : ℤ) := by
      zify [hq5, hr_ge, hs_ge] at h_div_3_Y'
      exact h_div_3_Y'
    exact (helper_ineq_contradiction (q : ℤ) (r : ℤ) (s : ℤ) hq_ge_int hr_ge_int hs_ge_int hq_lt_r_int hr_lt_s_int) h_div_3_Y'_int
  · have hq3 : q = 3 := by omega
    have hr_ge : 5 ≤ r := by
      rw [hq3] at hq_lt_r
      have : r ≠ 4 := by
        intro hc
        rw [hc] at hr_prime
        revert hr_prime; decide
      omega
    have hs_ge : 7 ≤ s := by
      have : r < s := hr_lt_s
      have : s ≠ 6 := by intro hc; rw [hc] at hs_prime; revert hs_prime; decide
      omega
    have h_gs_eq_rew : 6 * r * s * g_s_prime = 15 * (2 * r - 1) * (2 * s - 1) * Y' + 3 := by
      rw [hq3] at h_gs_eq
      rw [hY] at h_gs_eq
      have h_ring_LHS : 2 * 3 * r * s * g_s_prime = 6 * r * s * g_s_prime := by ring
      rw [h_ring_LHS] at h_gs_eq
      have h_ring_RHS : 3 * (2 * 3 - 1) * (2 * r - 1) * ((2 * s - 1) * Y') + 1 = 15 * (2 * r - 1) * (2 * s - 1) * Y' + 1 := by ring
      rw [h_ring_RHS] at h_gs_eq
      omega
    have h_le_54 : 6 * r * s * g_s_prime ≤ 54 * r * s * Y' := by
      have : 6 * r * s * g_s_prime = (6 * r * s) * g_s_prime := by ring
      rw [this]
      have h_mul := Nat.mul_le_mul_left (6 * r * s) h_gs_le_9
      have h_ring : 6 * r * s * (9 * Y') = 54 * r * s * Y' := by ring
      rw [h_ring] at h_mul
      exact h_mul
    have h_final_ineq : 15 * (2 * r - 1) * (2 * s - 1) * Y' + 3 ≤ 54 * r * s * Y' := by
      rwa [← h_gs_eq_rew]
    have h_strict_lt : 15 * (2 * r - 1) * (2 * s - 1) * Y' < 54 * r * s * Y' := by
      omega
    have h_div_3_Y' : 5 * (2 * r - 1) * (2 * s - 1) < 18 * r * s := by
      have h_mul_lt : 3 * (5 * (2 * r - 1) * (2 * s - 1)) * Y' < 3 * (18 * r * s) * Y' := by
        have : 3 * (18 * r * s) * Y' = 54 * r * s * Y' := by ring
        rw [this]
        have h_ring_LHS : 3 * (5 * (2 * r - 1) * (2 * s - 1)) * Y' = 15 * (2 * r - 1) * (2 * s - 1) * Y' := by ring
        rwa [h_ring_LHS]
      have h_3_Y'_pos : 0 < 3 * Y' := by omega
      have h_lt := Nat.lt_of_mul_lt_mul_right h_mul_lt
      exact h_lt
    have hr_ge_int : (5 : ℤ) ≤ (r : ℤ) := by zify; exact hr_ge
    have hs_ge_int : (7 : ℤ) ≤ (s : ℤ) := by zify; exact hs_ge
    have h_div_3_Y'_int : 5 * (2 * (r : ℤ) - 1) * (2 * (s : ℤ) - 1) < 18 * (r : ℤ) * (s : ℤ) := by
      zify [hr_ge, hs_ge] at h_div_3_Y'
      exact h_div_3_Y'
    exact (helper_ineq_contradiction_q3 (r : ℤ) (s : ℤ) hr_ge_int hs_ge_int hr_lt_s) h_div_3_Y'_int
