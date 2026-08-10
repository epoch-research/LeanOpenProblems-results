import FormalConjectures.Util.ProblemImports

lemma sq_sub_div_eq (n k : ℕ) (h : 2 * k ≤ n) : (n - k) ^ 2 / n = n - 2 * k + k ^ 2 / n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h_eq : (n - k) ^ 2 = (n - 2 * k) * n + k ^ 2 := by
      have h_int : (((n - k) ^ 2 : ℕ) : ℤ) = (((n - 2 * k) * n + k ^ 2 : ℕ) : ℤ) := by
        rw [Nat.cast_pow, Nat.cast_sub (by omega)]
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h, Nat.cast_pow]
        push_cast
        ring
      exact_mod_cast h_int
    rw [h_eq]
    have h_comm : (n - 2 * k) * n + k ^ 2 = k ^ 2 + n * (n - 2 * k) := by ring
    rw [h_comm, Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hn), add_comm]

lemma j_bound (n j : ℕ) (hn : 5 ≤ n) (hj : 2 * j ≤ n) : n + 3 * (j ^ 2 / n) + 1 ≥ 3 * j := by
  rcases lt_or_ge j 3 with hj3 | hj3
  · have : 3 * (j ^ 2 / n) ≥ 0 := by omega
    omega
  · by_cases hj_ge : 1 ≤ j ^ 2 / n
    · rcases lt_or_ge j 5 with hj5 | hj5
      · rcases eq_or_ne j 3 with rfl | hj4
        · by_cases hn9 : n ≤ 9
          · interval_cases n <;> decide
          · push_neg at hn9
            have : 3 ^ 2 / n = 0 := by
              rw [Nat.div_eq_of_lt]
              omega
            omega
        · have : j = 4 := by omega
          subst this
          by_cases hn16 : n ≤ 16
          · interval_cases n <;> decide
          · push_neg at hn16
            have : 4 ^ 2 / n = 0 := by
              rw [Nat.div_eq_of_lt]
              omega
            omega
      · have hj_div_ge : 2 ≤ j ^ 2 / n := by
          by_contra h_lt
          push_neg at h_lt
          have hj_sq_lt : j ^ 2 < 2 * n := by
            have hn0 : n > 0 := by omega
            have h_mul := Nat.div_le_iff_le_mul hn0 |>.mp h_lt
            calc j ^ 2 ≤ 1 * n := h_mul
            _ = n := by ring
            _ < 2 * n := by omega
          have hj_sq_ge : j ^ 2 ≥ 2 * n := by
            calc j ^ 2 = j * j := by ring
            _ ≥ 5 * j := Nat.mul_le_mul_right j hj5
            _ = 2 * (2 * j) + j := by ring
            _ ≥ 2 * n := by omega
          omega
        rcases lt_or_ge j 8 with hj8 | hj8
        · omega
        · have hj_div2 : 4 ≤ j ^ 2 / n := by
            by_contra h_lt
            push_neg at h_lt
            have hj_sq_lt : j ^ 2 < 4 * n := by
              have hn0 : n > 0 := by omega
              have h_mul := Nat.div_le_iff_le_mul hn0 |>.mp h_lt
              calc j ^ 2 ≤ 3 * n := h_mul
              _ < 4 * n := by omega
            have hj_sq_ge : j ^ 2 ≥ 4 * n := by
              calc j ^ 2 = j * j := by ring
              _ ≥ 8 * j := Nat.mul_le_mul_right j hj8
              _ = 4 * (2 * j) := by ring
              _ ≥ 4 * n := by omega
            omega
          rcases lt_or_ge j 14 with hj14 | hj14
          · omega
          · have hj_div3 : 7 ≤ j ^ 2 / n := by
              by_contra h_lt
              push_neg at h_lt
              have hj_sq_lt : j ^ 2 < 7 * n := by
                have hn0 : n > 0 := by omega
                have h_mul := Nat.div_le_iff_le_mul hn0 |>.mp h_lt
                calc j ^ 2 ≤ 6 * n := h_mul
                _ < 7 * n := by omega
              have hj_sq_ge : j ^ 2 ≥ 7 * n := by
                calc j ^ 2 = j * j := by ring
                _ ≥ 14 * j := Nat.mul_le_mul_right j hj14
                _ = 7 * (2 * j) := by ring
                _ ≥ 7 * n := by omega
              omega
            rcases lt_or_ge j 23 with hj23 | hj23
            · omega
            · have hj_div4 : 11 ≤ j ^ 2 / n := by
                by_contra h_lt
                push_neg at h_lt
                have hj_sq_lt : j ^ 2 < 11 * n := by
                  have hn0 : n > 0 := by omega
                  have h_mul := Nat.div_le_iff_le_mul hn0 |>.mp h_lt
                  calc j ^ 2 ≤ 10 * n := h_mul
                  _ < 11 * n := by omega
                have hj_sq_ge : j ^ 2 ≥ 11 * n := by
                  calc j ^ 2 = j * j := by ring
                  _ ≥ 23 * j := Nat.mul_le_mul_right j hj23
                  _ ≥ 22 * j := by omega
                  _ = 11 * (2 * j) := by ring
                  _ ≥ 11 * n := by omega
                omega
              rcases lt_or_ge j 35 with hj35 | hj35
              · omega
              · have hj_div5 : 17 ≤ j ^ 2 / n := by
                  by_contra h_lt
                  push_neg at h_lt
                  have hj_sq_lt : j ^ 2 < 17 * n := by
                    have hn0 : n > 0 := by omega
                    have h_mul := Nat.div_le_iff_le_mul hn0 |>.mp h_lt
                    calc j ^ 2 ≤ 16 * n := h_mul
                    _ < 17 * n := by omega
                  have hj_sq_ge : j ^ 2 ≥ 17 * n := by
                    calc j ^ 2 = j * j := by ring
                    _ ≥ 35 * j := Nat.mul_le_mul_right j hj35
                    _ ≥ 34 * j := by omega
                    _ = 17 * (2 * j) := by ring
                    _ ≥ 17 * n := by omega
                  omega
                rcases lt_or_ge j 53 with hj53 | hj53
                · omega
                · have hj_div6 : 26 ≤ j ^ 2 / n := by
                    by_contra h_lt
                    push_neg at h_lt
                    have hj_sq_lt : j ^ 2 < 26 * n := by
                      have hn0 : n > 0 := by omega
                      have h_mul := Nat.div_le_iff_le_mul hn0 |>.mp h_lt
                      calc j ^ 2 ≤ 25 * n := h_mul
                      _ < 26 * n := by omega
                    have hj_sq_ge : j ^ 2 ≥ 26 * n := by
                      calc j ^ 2 = j * j := by ring
                      _ ≥ 53 * j := Nat.mul_le_mul_right j hj53
                      _ ≥ 52 * j := by omega
                      _ = 26 * (2 * j) := by ring
                      _ ≥ 26 * n := by omega
                    omega
                  omega
    · push_neg at hj_ge
      have hj_eq0 : j ^ 2 / n = 0 := by omega
      have hj_sq_lt : j ^ 2 < n := by
        have hn0 : n > 0 := by omega
        rw [Nat.div_eq_zero_iff] at hj_eq0
        · exact hj_eq0
        · omega
      have hn_ge : n ≥ 2 * j + 2 := by
        have h_trans : 2 * j + 2 ≤ j ^ 2 := by
          calc 2 * j + 2 ≤ 2 * j + j := by omega
          _ = 3 * j := by ring
          _ ≤ j * j := Nat.mul_le_mul_right j hj3
          _ = j ^ 2 := by ring
        omega
      omega
