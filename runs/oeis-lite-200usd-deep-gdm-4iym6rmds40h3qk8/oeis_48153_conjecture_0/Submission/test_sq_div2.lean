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
  · rcases lt_or_ge j 6 with hj6 | hj6
    · rcases eq_or_ne j 3 with rfl | hj3_ne
      · by_cases hn9 : n ≤ 9
        · interval_cases n <;> decide
        · push_neg at hn9
          have : 3 ^ 2 / n = 0 := by
            rw [Nat.div_eq_of_lt]
            omega
          rw [this]
          omega
      · rcases eq_or_ne j 4 with rfl | hj4_ne
        · by_cases hn16 : n ≤ 16
          · interval_cases n <;> decide
          · push_neg at hn16
            have : 4 ^ 2 / n = 0 := by
              rw [Nat.div_eq_of_lt]
              omega
            omega
        · have : j = 5 := by omega
          subst this
          by_cases hn25 : n ≤ 25
          · interval_cases n <;> decide
          · push_neg at hn25
            have : 5 ^ 2 / n = 0 := by
              rw [Nat.div_eq_of_lt]
              omega
            omega
    · by_cases h_le : 3 * j ≤ n + 1
      · omega
      · push_neg at h_le
        have hj_sq_ge : j ^ 2 ≥ 2 * n := by
          calc j ^ 2 = j * j := by ring
          _ ≥ 6 * j := Nat.mul_le_mul_right j hj6
          _ = 2 * (3 * j) := by ring
          _ ≥ 2 * (n + 2) := by omega
          _ ≥ 2 * n := by omega
        have hj_div_ge : 2 ≤ j ^ 2 / n := by
          rw [Nat.le_div_iff_mul_le (by omega)]
          omega
        rcases lt_or_ge j 8 with hj8 | hj8
        · omega
        · have hj_sq2 : j ^ 2 ≥ 4 * n := by
            calc j ^ 2 = j * j := by ring
            _ ≥ 8 * j := Nat.mul_le_mul_right j hj8
            _ = 4 * (2 * j) := by ring
            _ ≥ 4 * n := by omega
          have hj_div2 : 4 ≤ j ^ 2 / n := by
            rw [Nat.le_div_iff_mul_le (by omega)]
            omega
          rcases lt_or_ge j 14 with hj14 | hj14
          · omega
          · have hj_sq3 : j ^ 2 ≥ 7 * n := by
              calc j ^ 2 = j * j := by ring
              _ ≥ 14 * j := Nat.mul_le_mul_right j hj14
              _ = 7 * (2 * j) := by ring
              _ ≥ 7 * n := by omega
            have hj_div3 : 7 ≤ j ^ 2 / n := by
              rw [Nat.le_div_iff_mul_le (by omega)]
              omega
            rcases lt_or_ge j 23 with hj23 | hj23
            · omega
            · have hj_sq4 : j ^ 2 ≥ 11 * n := by
                calc j ^ 2 = j * j := by ring
                _ ≥ 23 * j := Nat.mul_le_mul_right j hj23
                _ ≥ 22 * j := by omega
                _ = 11 * (2 * j) := by ring
                _ ≥ 11 * n := by omega
              have hj_div4 : 11 ≤ j ^ 2 / n := by
                rw [Nat.le_div_iff_mul_le (by omega)]
                omega
              rcases lt_or_ge j 35 with hj35 | hj35
              · omega
              · have hj_sq5 : j ^ 2 ≥ 17 * n := by
                  calc j ^ 2 = j * j := by ring
                  _ ≥ 35 * j := Nat.mul_le_mul_right j hj35
                  _ ≥ 34 * j := by omega
                  _ = 17 * (2 * j) := by ring
                  _ ≥ 17 * n := by omega
                have hj_div5 : 17 ≤ j ^ 2 / n := by
                  rw [Nat.le_div_iff_mul_le (by omega)]
                  omega
                rcases lt_or_ge j 53 with hj53 | hj53
                · omega
                · have hj_sq6 : j ^ 2 ≥ 26 * n := by
                    calc j ^ 2 = j * j := by ring
                    _ ≥ 53 * j := Nat.mul_le_mul_right j hj53
                    _ ≥ 52 * j := by omega
                    _ = 26 * (2 * j) := by ring
                    _ ≥ 26 * n := by omega
                  have hj_div6 : 26 ≤ j ^ 2 / n := by
                    rw [Nat.le_div_iff_mul_le (by omega)]
                    omega
                  omega

lemma paired_bound (n j : ℕ) (hn : 5 ≤ n) (hj : 2 * j ≤ n) : 
    3 * ((n - j) ^ 2 / n + j ^ 2 / n) ≥ 2 * n - 4 * j + 2 := by
  have h_eq : (n - j) ^ 2 / n = n - 2 * j + j ^ 2 / n := sq_sub_div_eq n j hj
  rw [h_eq]
  have h_mul : 3 * (n - 2 * j + j ^ 2 / n + j ^ 2 / n) = 3 * (n - 2 * j) + 6 * (j ^ 2 / n) := by
    omega
  rw [h_mul]
  have h_dist : 3 * (n - 2 * j) = 3 * n - 6 * j := by omega
  rw [h_dist]
  have h_j := j_bound n j hn hj
  omega