import FormalConjectures.Util.ProblemImports

open Finset

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

lemma j_bound_new (n j : ℕ) (hn : 5 ≤ n) (hj : 2 * j ≤ n) : 3 * (j^2 / n) + n + 1 ≥ 3 * j := by
  by_cases hj_lt : 3 * j ≤ n + 1
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
    have h_eq : n * (3 * j) ≤ n * (3 * (j^2 / n) + n + 1) := by
      calc n * (3 * j) = 3 * j * n := by ring
      _ ≤ 3 * n * (j^2 / n) + n^2 + n := h_mul
      _ = n * (3 * (j^2 / n) + n + 1) := by ring
    have hn_pos : n > 0 := by omega
    exact Nat.le_of_mul_le_mul_left h_eq hn_pos

lemma j_bound_stronger (n j : ℕ) (hn : 6 ≤ n) (hj : 2 * j ≤ n) : 6 * (j^2 / n) + n ≥ 3 * j := by
  by_cases h_div : j^2 / n ≥ 1
  · have h_j := j_bound_new n j (by omega) hj
    calc 6 * (j^2 / n) + n = 3 * (j^2 / n) + 3 * (j^2 / n) + n := by ring
    _ ≥ 3 * (j^2 / n) + n + 3 := by omega
    _ ≥ 3 * j + 2 := by omega
    _ ≥ 3 * j := by omega
  · push_neg at h_div
    have h_div0 : j^2 / n = 0 := by
      generalize j^2 / n = X at *
      omega
    rw [h_div0, mul_zero, zero_add]
    have h_sq_lt : j^2 < n := by
      by_contra h_ge
      push_neg at h_ge
      have : j^2 / n ≥ 1 := Nat.div_pos h_ge (by omega)
      omega
    rcases lt_or_ge j 3 with hj3 | hj3
    · interval_cases j
      · omega
      · omega
      · omega
    · have h_j2 : j^2 ≥ 3 * j := by
        calc j^2 = j * j := by ring
        _ ≥ 3 * j := Nat.mul_le_mul_right j hj3
      omega

lemma k_bound_stronger (n k : ℕ) (hn : 6 ≤ n) (hk : k < n) : 6 * (k^2 / n) + n ≥ 3 * k := by
  by_cases h_le : 2 * k ≤ n
  · exact j_bound_stronger n k hn h_le
  · push_neg at h_le
    have hj : 2 * (n - k) ≤ n := by omega
    have h_j := j_bound_stronger n (n - k) hn hj
    have h_div := sq_sub_div_eq n (n - k) hj
    have h_sub : n - (n - k) = k := by omega
    rw [h_sub] at h_div
    omega
