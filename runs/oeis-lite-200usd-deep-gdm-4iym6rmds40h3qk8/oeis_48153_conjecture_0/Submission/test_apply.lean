import FormalConjectures.Util.ProblemImports

open Finset

lemma sum_range_sq (n : ℕ) : 6 * ∑ i ∈ range n, i ^ 2 = (n - 1) * n * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    rcases n with _ | n
    · simp
    · -- n is succ n. So n ≥ 1. Let's rewrite subtraction away.
      have h1 : n.succ - 1 = n := by omega
      have h2 : 2 * n.succ - 1 = 2 * n + 1 := by omega
      rw [h1, h2]
      have h_int : (((n * n.succ * (2 * n + 1) + 6 * n.succ ^ 2 : ℕ) : ℤ) = ((n.succ * (n.succ + 1) * (2 * n.succ + 1) : ℕ) : ℤ)) := by
        push_cast
        ring
      exact_mod_cast h_int

lemma sum_sq_div_reflect (n : ℕ) : ∑ k ∈ range n, ((n - 1 - k) ^ 2 / n) = ∑ k ∈ range n, (k ^ 2 / n) := by
  exact sum_range_reflect (fun i => i ^ 2 / n) n

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

lemma sq_sub_div_ge (n k : ℕ) (h : k ≤ n) : (n - k) ^ 2 / n ≥ n - 2 * k := by
  by_cases h_le : 2 * k ≤ n
  · rw [sq_sub_div_eq n k h_le]
    exact Nat.le_add_right (n - 2 * k) (k ^ 2 / n)
  · have : n - 2 * k = 0 := by omega
    rw [this]
    exact Nat.zero_le _

lemma key_ineq (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : 3 * (k ^ 2 / n) + n ≥ 2 * k + 1 := by
  by_cases h_le : 2 * k + 1 ≤ n
  · omega
  · push_neg at h_le
    have h_sub_le : 2 * (n - k) ≤ n := by omega
    have h_k_eq : k = n - (n - k) := by omega
    nth_rw 1 [h_k_eq]
    rw [sq_sub_div_eq n (n - k) h_sub_le]
    have h_div_ge : (n - k) ^ 2 / n ≥ 0 := Nat.zero_le _
    by_cases h_eq : 2 * k = n
    · have h_k : k = n / 2 := by omega
      have : (n - k) ^ 2 / n ≥ 1 := by
        have h_eq2 : n - k = n / 2 := by omega
        rw [h_eq2]
        have h_pos : 0 < n := by omega
        have h_le2 : n ≤ (n / 2) ^ 2 := by
          have h_half : 2 ≤ n / 2 := by omega
          calc n = 2 * (n / 2) := (Nat.mul_div_cancel' (by omega)).symm
          _ ≤ (n / 2) * (n / 2) := Nat.mul_le_mul_right (n / 2) h_half
          _ = (n / 2) ^ 2 := by ring
        exact Nat.div_pos h_le2 h_pos
      omega
    · omega

lemma k_mul_sub_le_n_mul_sub (n k : ℕ) (hk : k < n) : 2 * (k * (n - k)) ≤ n * (n - 1) := by
  have h_le : n ≤ (n - k) ^ 2 + k ^ 2 := by
    rcases k with _ | k
    · simp
      have : n ≤ n ^ 2 := by
        rcases n with _ | n
        · simp
        · nlinarith
      omega
    · have h1 : n - k.succ ≥ 1 := by omega
      have h2 : k.succ ≥ 1 := by omega
      have h3 : (n - k.succ) ≤ (n - k.succ) ^ 2 := by nlinarith
      have h4 : k.succ ≤ k.succ ^ 2 := by nlinarith
      omega
  have h_eq : (n - k) ^ 2 + k ^ 2 + 2 * k * (n - k) = n ^ 2 := by
    have h_int : (((n - k) ^ 2 + k ^ 2 + 2 * k * (n - k) : ℕ) : ℤ) = ((n ^ 2 : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
      ring
    exact_mod_cast h_int
  have h_sq : n * (n - 1) = n ^ 2 - n := by
    rw [Nat.mul_sub_left_distrib, mul_one, sq]
  rw [h_sq]
  omega







