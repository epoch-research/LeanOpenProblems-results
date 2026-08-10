import FormalConjectures.Util.ProblemImports

lemma j_bound_strongest (n j : ℕ) (hn : 5 ≤ n) (hj : 2 * j ≤ n) : 3 * (j^2 / n) + 3 * ((n + 1) / 3) ≥ 3 * j := by
  by_cases hj_lt : 3 * j ≤ 3 * ((n + 1) / 3)
  · omega
  · push_neg at hj_lt
    have h_quad : 3 * j * n + 2 * n ≤ 3 * j^2 + n^2 + 3 := by
      nlinarith
    have h_div : j^2 = n * (j^2 / n) + j^2 % n := (Nat.div_add_mod (j^2) n).symm
    have h_mod_lt : j^2 % n < n := Nat.mod_lt _ (by omega)
    have h_mod_le : 3 * (j^2 % n) + 3 ≤ 3 * n := by omega
    have h_sq_le : 3 * j^2 + 3 ≤ 3 * n * (j^2 / n) + 3 * n := by
      calc 3 * j^2 + 3 = 3 * (n * (j^2 / n) + j^2 % n) + 3 := by rw [← h_div]
      _ = 3 * n * (j^2 / n) + (3 * (j^2 % n) + 3) := by ring
      _ ≤ 3 * n * (j^2 / n) + 3 * n := Nat.add_le_add_left h_mod_le _
    have h_mul : 3 * j * n ≤ 3 * n * (j^2 / n) + n^2 + n := by
      have h_comb : 3 * j * n + 2 * n ≤ 3 * n * (j^2 / n) + 3 * n + n^2 := by
        calc 3 * j * n + 2 * n ≤ 3 * j^2 + 3 + n^2 := by omega
        _ ≤ 3 * n * (j^2 / n) + 3 * n + n^2 := Nat.add_le_add_right h_sq_le _
      omega
    have h_div2 : n + 1 = 3 * ((n + 1) / 3) + (n + 1) % 3 := (Nat.div_add_mod (n + 1) 3).symm
    have h_mod_lt2 : (n + 1) % 3 < 3 := Nat.mod_lt _ (by omega)
    have h_eq : n * (3 * j) ≤ n * (3 * (j^2 / n) + 3 * ((n + 1) / 3)) := by
      calc n * (3 * j) = 3 * j * n := by ring
      _ ≤ 3 * n * (j^2 / n) + n^2 + n := h_mul
      _ = 3 * n * (j^2 / n) + n * (n + 1) := by ring
      _ = 3 * n * (j^2 / n) + n * (3 * ((n + 1) / 3) + (n + 1) % 3) := by rw [h_div2]
      _ ≤ 3 * n * (j^2 / n) + n * (3 * ((n + 1) / 3) + 2) := by omega
      _ = n * (3 * (j^2 / n) + 3 * ((n + 1) / 3)) + 2 * n := by ring
      _ ≤ n * (3 * (j^2 / n) + 3 * ((n + 1) / 3)) + n * (3 * j - 3 * ((n + 1) / 3)) := by
        -- Since 3 * j > 3 * ((n + 1)/3), we have 3 * j - 3 * ((n + 1)/3) ≥ 1.
        -- And n ≥ 5, so we can prove this!
        have : 3 * j - 3 * ((n + 1) / 3) ≥ 1 := by omega
        have : 3 * j - 3 * ((n + 1) / 3) ≥ 2 := by
          -- Wait!
          -- 3 * j and 3 * ((n + 1)/3) are both multiples of 3!
          -- So their difference is also a multiple of 3!
          -- Since it is ≥ 1, it must be ≥ 3!
          -- So 3 * j - 3 * ((n + 1)/3) ≥ 3!
          omega
        nlinarith
      _ = n * (3 * j) := by ring
    have hn_pos : n > 0 := by omega
    exact Nat.le_of_mul_le_mul_left h_eq hn_pos
