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

lemma sq_div_ge (n k : ℕ) (hk : k < n) : 3 * (k ^ 2 / n) + 2 * n ≥ 4 * k := by
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

lemma sum_sq_div_ge (n : ℕ) : 3 * (∑ k ∈ range n, (k ^ 2 / n)) + 2 * n * n ≥ 2 * n * (n - 1) := by
  have h : ∑ k ∈ range n, (3 * (k ^ 2 / n) + 2 * n) ≥ ∑ k ∈ range n, (4 * k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    exact sq_div_ge n k hk_lt
  have h_lhs : ∑ k ∈ range n, (3 * (k ^ 2 / n) + 2 * n) = 3 * (∑ k ∈ range n, (k ^ 2 / n)) + 2 * n * n := by
    rw [sum_add_distrib, ← Finset.mul_sum, sum_const]
    simp
    ring
  have h_rhs : ∑ k ∈ range n, (4 * k) = 2 * n * (n - 1) := by
    rw [← Finset.mul_sum, sum_range_id]
    have h_even : 2 ∣ n * (n - 1) := by
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have : k + k = 2 * k := by omega
        rw [this, mul_assoc]
        exact dvd_mul_right 2 _
      · have : 2 * k + 1 - 1 = 2 * k := by omega
        rw [this, mul_comm, mul_assoc]
        exact dvd_mul_right 2 _
    have h_cancel := Nat.mul_div_cancel' h_even
    have h_assoc : 2 * n * (n - 1) = 2 * (n * (n - 1)) := by ring
    rw [h_assoc]
    generalize h_Y : n * (n - 1) / 2 = Y
    generalize h_Z : n * (n - 1) = Z at *
    omega
  rw [h_lhs, h_rhs] at h
  exact h

