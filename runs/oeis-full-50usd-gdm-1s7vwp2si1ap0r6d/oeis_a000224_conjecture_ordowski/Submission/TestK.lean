import FormalConjectures.Util.ProblemImports

theorem k_lt_4_impossible {n A M k_val : ℕ} (hA : A ≤ (n - 1) / 2) (hM : M = A * (A - 1)) (hk : n * n - 1 = k_val * M) (hn : 2 ≤ n) (hk_lt : k_val ≤ 3) : False := by
  have h1 : 2 * A ≤ n - 1 := by
    have : 2 * A ≤ 2 * ((n - 1) / 2) := Nat.mul_le_mul_left 2 hA
    have h_div : 2 * ((n - 1) / 2) ≤ n - 1 := Nat.mul_div_le (n - 1) 2
    omega
  rcases n with _ | _ | m
  · omega
  · omega
  · -- n = m + 2
    have h_sub1 : m + 2 - 1 = m + 1 := by omega
    have h_mul1 : (m + 2) * (m + 2) = (m * m) + 4 * m + 4 := by ring
    have h_sub2 : (m + 2) * (m + 2) - 1 = (m * m) + 4 * m + 3 := by
      rw [h_mul1]
      omega
    have h_calc : 4 * ((m + 2) * (m + 2) - 1) ≤ 3 * (m + 2 - 1) * (m + 2 - 1) := by
      calc
        4 * ((m + 2) * (m + 2) - 1) = 4 * (k_val * M) := by rw [hk]
        _ = 4 * k_val * (A * (A - 1)) := by
          rw [hM]
          ring
        _ ≤ 4 * 3 * (A * (A - 1)) := Nat.mul_le_mul_right (A * (A - 1)) (Nat.mul_le_mul_left 4 hk_lt)
        _ = 12 * A * (A - 1) := by ring
        _ ≤ 12 * A * A := by
          have : A - 1 ≤ A := by omega
          nlinarith
        _ = 3 * (2 * A) * (2 * A) := by ring
        _ ≤ 3 * (m + 2 - 1) * (m + 2 - 1) := by
          have : 2 * A ≤ m + 2 - 1 := h1
          nlinarith
    have h_lhs : 4 * ((m + 2) * (m + 2) - 1) = 4 * (m * m) + 16 * m + 12 := by
      rw [h_sub2]
      ring
    have h_rhs : 3 * (m + 2 - 1) * (m + 2 - 1) = 3 * (m * m) + 6 * m + 3 := by
      rw [h_sub1]
      ring
    rw [h_lhs, h_rhs] at h_calc
    clear h1 h_sub1 h_mul1 h_sub2 h_lhs h_rhs hM hk
    generalize m * m = x at h_calc
    omega
