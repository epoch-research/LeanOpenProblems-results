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

lemma paired_bound_better (n j : ℕ) (hn : 6 ≤ n) (hj : 2 * j ≤ n) :
    3 * ((n - j) ^ 2 / n + j ^ 2 / n) ≥ 
      if 3 * j ≤ n + 1 then 
        (if j ^ 2 ≥ n then 3 * n - 6 * j + 6 else 3 * n - 6 * j)
      else n - 2 := by
  split_ifs with h1 h2
  · -- 3 * j ≤ n + 1 and j^2 ≥ n
    have h_eq : (n - j) ^ 2 / n = n - 2 * j + j ^ 2 / n := sq_sub_div_eq n j hj
    rw [h_eq]
    have h_div : j^2 / n ≥ 1 := Nat.div_pos h2 (by omega)
    generalize j^2 / n = X at *
    omega
  · -- 3 * j ≤ n + 1 and j^2 < n
    have h_eq : (n - j) ^ 2 / n = n - 2 * j + j ^ 2 / n := sq_sub_div_eq n j hj
    rw [h_eq]
    generalize j ^ 2 / n = X
    omega
  · -- 3 * j > n + 1
    have h_eq : (n - j) ^ 2 / n = n - 2 * j + j ^ 2 / n := sq_sub_div_eq n j hj
    rw [h_eq]
    generalize h_X : j ^ 2 / n = X
    have : 3 * (n - 2 * j + X + X) = 3 * (n - 2 * j) + 6 * X := by omega
    rw [this]
    have h_j' : 3 * X + n + 1 ≥ 3 * j := by
      rw [← h_X]
      exact j_bound_new n j (by omega) hj
    omega
