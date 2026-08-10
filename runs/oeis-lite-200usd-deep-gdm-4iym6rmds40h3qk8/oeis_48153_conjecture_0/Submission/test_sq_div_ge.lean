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

lemma sq_div_ge_stronger (n k : ℕ) (hn : 6 ≤ n) (hk : k < n) : 3 * (k ^ 2 / n) + 2 * n ≥ 4 * k + 2 := by
  by_cases h_le : 2 * k ≤ n
  · rcases eq_or_ne k 0 with rfl | hk_ne
    · simp; omega
    · have : 3 * (k^2 / n) ≥ 0 := by omega
      have h_eq : 2 * n = 4 * k + 2 * (n - 2 * k) := by omega
      by_cases h_eq2 : n = 2 * k
      · subst h_eq2
        have : k ≥ 3 := by omega
        have h_sq : k^2 / (2 * k) = k / 2 := by
          have h1 : k^2 = k * k := by ring
          have h2 : 2 * k = k * 2 := by ring
          rw [h1, h2]
          exact Nat.mul_div_mul_left k 2 (by omega)
        rw [h_sq]
        omega
      · omega
  · push_neg at h_le
    have h_sub_le : 2 * (n - k) ≤ n := by omega
    have h_eq : k ^ 2 / n = n - 2 * (n - k) + (n - k) ^ 2 / n := by
      have : k = n - (n - k) := by omega
      nth_rw 1 [this]
      exact sq_sub_div_eq n (n - k) h_sub_le
    rw [h_eq]
    generalize h_X : (n - k) ^ 2 / n = X
    by_cases hX : X ≥ 1
    · omega
    · push_neg at hX
      have h_X0 : X = 0 := by omega
      have h_sq_lt : (n - k)^2 < n := by
        by_contra h_ge
        push_neg at h_ge
        have h_div_ge : (n - k) ^ 2 / n ≥ 1 := Nat.div_pos h_ge (by omega)
        rw [h_X] at h_div_ge
        omega
      rcases lt_or_ge (n - k) 3 with h_nk3 | h_nk3
      · interval_cases j_val : n - k
        · -- n - k = 0 => k = n, impossible
          omega
        · -- n - k = 1 => k = n - 1.
          omega
        · -- n - k = 2 => k = n - 2.
          omega
      · have h_trans : 2 * (n - k) + 2 ≤ (n - k)^2 + 1 := by nlinarith
        have h_final : 2 * (n - k) + 2 ≤ n := by omega
        omega
