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

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma A048153_eq_sum_sub (n : ℕ) : 
    ((A048153 n : ℕ) : ℤ) = ((∑ k ∈ range n, k^2 : ℕ) : ℤ) - n * ((∑ k ∈ range n, (k^2 / n) : ℕ) : ℤ) := by
  have h_sum : ((A048153 n : ℕ) : ℤ) = ∑ k ∈ range n, (((k^2 % n : ℕ) : ℤ)) := by
    simp [A048153]
  rw [h_sum]
  have h_term (k : ℕ) : ((k^2 % n : ℕ) : ℤ) = ((k^2 : ℕ) : ℤ) - (n : ℤ) * ((k^2 / n : ℕ) : ℤ) := by
    have h_div_mod : k^2 = n * (k^2 / n) + k^2 % n := (Nat.div_add_mod (k^2) n).symm
    have h_div_mod_cast : ((k^2 : ℕ) : ℤ) = (n : ℤ) * ((k^2 / n : ℕ) : ℤ) + ((k^2 % n : ℕ) : ℤ) := by
      exact_mod_cast h_div_mod
    omega
  have h_sub : (fun k => ((k^2 % n : ℕ) : ℤ)) = (fun k => ((k^2 : ℕ) : ℤ) - (n : ℤ) * ((k^2 / n : ℕ) : ℤ)) := by
    funext k
    exact h_term k
  rw [h_sub]
  rw [sum_sub_distrib]
  rw [← Finset.mul_sum]
  push_cast
  rfl

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

lemma k_bound_universal (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : 3 * (k^2 / n) + n + 1 ≥ 3 * k := by
  by_cases h_le : 2 * k ≤ n
  · exact j_bound_new n k hn h_le
  · push_neg at h_le
    have hj : 2 * (n - k) ≤ n := by omega
    have h_j := j_bound_new n (n - k) hn hj
    have h_div := sq_sub_div_eq n (n - k) hj
    have h_sub : n - (n - k) = k := by omega
    rw [h_sub] at h_div
    omega

lemma sum_k_bound (n : ℕ) (hn : 5 ≤ n) : 3 * (∑ k ∈ range n, k^2 / n) + n * (n + 1) ≥ 3 * (n * (n - 1) / 2) := by
  have h_sum : ∑ k ∈ range n, (3 * (k^2 / n) + n + 1) ≥ ∑ k ∈ range n, 3 * k := by
    apply Finset.sum_le_sum
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    exact k_bound_universal n k hn hk_lt
  have h_lhs : ∑ k ∈ range n, (3 * (k^2 / n) + n + 1) = 3 * (∑ k ∈ range n, k^2 / n) + n * (n + 1) := by
    rw [sum_add_distrib, sum_add_distrib]
    rw [← mul_sum, sum_const, sum_const]
    simp
    ring
  have h_rhs : ∑ k ∈ range n, 3 * k = 3 * (n * (n - 1) / 2) := by
    rw [← mul_sum, sum_range_id]
  rw [h_lhs, h_rhs] at h_sum
  exact h_sum

lemma A048153_le_n_mul_sub (n : ℕ) (hn : 5 ≤ n) : A048153 n ≤ n * (n - 1) / 2 := by
  have h_even : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have : k + k = 2 * k := by omega
      rw [this, mul_assoc]
      exact dvd_mul_right 2 _
    · have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this, mul_comm, mul_assoc]
      exact dvd_mul_right 2 _
  have h_cancel : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' h_even

  have h_id := A048153_eq_sum_sub n
  have h_sq : 6 * ∑ k ∈ range n, k^2 = (n - 1) * n * (2 * n - 1) := sum_range_sq n
  have h_sum := sum_k_bound n hn

  have h_id_cast : ((A048153 n : ℕ) : ℤ) = ((∑ k ∈ range n, k^2 : ℕ) : ℤ) - (n : ℤ) * ((∑ k ∈ range n, (k^2 / n) : ℕ) : ℤ) := by
    exact_mod_cast h_id

  have h_sq_cast : 6 * ((∑ k ∈ range n, k^2 : ℕ) : ℤ) = ((n - 1 : ℕ) : ℤ) * (n : ℤ) * ((2 * n - 1 : ℕ) : ℤ) := by
    exact_mod_cast h_sq

  have h_sum_cast : 3 * ((∑ k ∈ range n, k^2 / n : ℕ) : ℤ) + (n : ℤ) * ((n : ℤ) + 1) ≥ 3 * (((n * (n - 1) / 2 : ℕ) : ℤ)) := by
    exact_mod_cast h_sum

  have h_cancel_cast : 2 * (((n * (n - 1) / 2 : ℕ) : ℤ)) = (n : ℤ) * ((n - 1 : ℕ) : ℤ) := by
    exact_mod_cast h_cancel

  have h1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (by omega)
  have h2 : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := Nat.cast_sub (by omega)

  have hn_cast : (n : ℤ) ≥ 5 := by omega

  have h_goal : 6 * ((A048153 n : ℕ) : ℤ) ≤ 3 * (n : ℤ) * ((n : ℤ) - 1) := by
    nlinarith [h_id_cast, h_sq_cast, h_sum_cast, h_cancel_cast, h1, h2, hn_cast]

  have h_goal_nat : 6 * A048153 n ≤ 3 * (n * (n - 1)) := by
    have : 3 * (n : ℤ) * ((n : ℤ) - 1) = (((3 * (n * (n - 1)) : ℕ) : ℤ)) := by
      push_cast
      rw [h1]
      ring
    rw [this] at h_goal
    exact_mod_cast h_goal

  have h_goal_final : 2 * A048153 n ≤ n * (n - 1) := by
    omega

  exact Nat.le_of_mul_le_mul_left (by omega) (by omega)
