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

lemma sq_div_ge_strong (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : 3 * (k ^ 2 / n) + n + 2 ≥ 3 * k := by
  by_cases h_le : 2 * k ≤ n
  · omega
  · push_neg at h_le
    have h_sub_le : 2 * (n - k) ≤ n := by omega
    have h_eq : k ^ 2 / n = n - 2 * (n - k) + (n - k) ^ 2 / n := by
      have : k = n - (n - k) := by omega
      nth_rw 1 [this]
      exact sq_sub_div_eq n (n - k) h_sub_le
    rw [h_eq]
    generalize (n - k) ^ 2 / n = X
    omega
