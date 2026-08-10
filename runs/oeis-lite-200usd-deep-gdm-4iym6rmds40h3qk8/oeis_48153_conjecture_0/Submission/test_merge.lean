import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

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

lemma A048153_add_div_eq_sq (n : ℕ) :
    A048153 n + n * ∑ k ∈ range n, k^2 / n = ∑ k ∈ range n, k^2 := by
  unfold A048153
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  exact Nat.mod_add_div (k^2) n

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

lemma k_sq_div_piecewise (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) :
    3 * (k ^ 2 / n) ≥ if 3 * k ≥ n + 1 then 3 * k - n - 1 else 0 := by
  split_ifs with h
  · have h_univ := k_bound_universal n k hn hk
    omega
  · omega

def S_term (n k : ℕ) : ℕ := if 3 * k ≥ n + 1 then 9 * k - 3 * n - 3 else 0

def S_sum (n : ℕ) : ℕ := ∑ k ∈ range n, S_term n k

lemma S_term_identity (n k : ℕ) (hk : k < n) :
    S_term (n + 1) k + (if 3 * k ≥ (n + 1) + 1 then 3 else 0) = S_term n k := by
  unfold S_term
  split_ifs with h1 h2
  · omega
  · omega
  · omega
  · omega

lemma S_sum_identity (n : ℕ) :
    (∑ k ∈ range n, S_term (n + 1) k) + ∑ k ∈ range n, (if 3 * k ≥ (n + 1) + 1 then 3 else 0) = ∑ k ∈ range n, S_term n k := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_lt : k < n := Finset.mem_range.mp hk
  exact S_term_identity n k hk_lt

lemma S_sum_succ (n : ℕ) (hn : 1 ≤ n) :
    S_sum (n + 1) = (∑ k ∈ range n, S_term (n + 1) k) + (6 * n - 6) := by
  rw [S_sum, sum_range_succ]
  have h_term : S_term (n + 1) n = 6 * n - 6 := by
    unfold S_term
    have : 3 * n ≥ (n + 1) + 1 := by omega
    simp [this]
    omega
  rw [h_term]

lemma S_sum_relation (n : ℕ) (hn : 1 ≤ n) :
    S_sum (n + 1) + ∑ k ∈ range n, (if 3 * k ≥ (n + 1) + 1 then 3 else 0) = S_sum n + 6 * n - 6 := by
  have h_succ := S_sum_succ n hn
  have h_id := S_sum_identity n
  unfold S_sum at *
  omega

lemma C_sum_bound (n : ℕ) :
    ∑ k ∈ range n, (if 3 * k ≥ (n + 1) + 1 then 3 else 0) ≤ 3 * n := by
  have h_le : ∑ k ∈ range n, (if 3 * k ≥ (n + 1) + 1 then 3 else 0) ≤ ∑ k ∈ range n, 3 := by
    apply Finset.sum_le_sum
    intro k hk
    split_ifs <;> omega
  have h2 : ∑ k ∈ range n, 3 = 3 * n := by
    simp
    rw [mul_comm]
  omega

lemma succ_prod_identity (n : ℕ) (hn : 5 ≤ n) : (n + 1 - 1) * (n + 1 - 2) = n * (n - 1) := by
  have h1 : n + 1 - 1 = n := by omega
  have h2 : n + 1 - 2 = n - 1 := by omega
  rw [h1, h2]

theorem S_sum_ge_target (n : ℕ) (hn : 5 ≤ n) : S_sum n ≥ (n - 1) * (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base =>
    decide
  | succ n hn ih =>
    have h_rel := S_sum_relation n (by omega)
    have h_bound := C_sum_bound n
    have h_sub : 3 * n ≤ 4 * n - 4 := by omega
    -- We rewrite to avoid subtraction before casting
    have h_rel_add : S_sum (n + 1) + (∑ k ∈ range n, if 3 * k ≥ (n + 1) + 1 then 3 else 0) + 6 = S_sum n + 6 * n := by
      omega
    have h_rel_cast : (S_sum (n + 1) : ℤ) + ((∑ k ∈ range n, (if 3 * k ≥ (n + 1) + 1 then 3 else 0) : ℕ) : ℤ) + 6 = (S_sum n : ℤ) + 6 * (n : ℤ) := by
      exact_mod_cast h_rel_add
    have h_bound_cast : ((∑ k ∈ range n, (if 3 * k ≥ (n + 1) + 1 then 3 else 0) : ℕ) : ℤ) ≤ 3 * (n : ℤ) := by
      exact_mod_cast h_bound
    have h_sub_cast : 3 * (n : ℤ) ≤ 4 * (n : ℤ) - 4 := by
      omega
    have h_ih_cast : (S_sum n : ℤ) ≥ ((n - 1 : ℕ) : ℤ) * ((n - 2 : ℕ) : ℤ) := by
      exact_mod_cast ih
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (by omega)
    have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Nat.cast_sub (by omega)
    have h_goal_cast : (S_sum (n + 1) : ℤ) ≥ (n : ℤ) * ((n : ℤ) - 1) := by
      nlinarith
    have h_goal_final : S_sum (n + 1) ≥ n * (n - 1) := by
      have h_int_cast : ((S_sum (n + 1) : ℕ) : ℤ) ≥ ((n * (n - 1) : ℕ) : ℤ) := by
        push_cast
        rw [Nat.cast_sub (by omega)]
        exact h_goal_cast
      exact_mod_cast h_int_cast
    rw [succ_prod_identity n hn]
    exact h_goal_final

lemma S_lower_bound (n : ℕ) (hn : 5 ≤ n) : 
    9 * (∑ k ∈ range n, k^2 / n) ≥ S_sum n := by
  have h_sum : 9 * (∑ k ∈ range n, k^2 / n) ≥ S_sum n := by
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    have h_piece := k_sq_div_piecewise n k hn hk_lt
    have h_term_mul : 9 * (k^2 / n) = 3 * (3 * (k^2 / n)) := by ring
    rw [h_term_mul]
    unfold S_term
    split_ifs with h
    · split_ifs at h_piece
      omega
    · omega
  exact h_sum

lemma S_lower_bound_target (n : ℕ) (hn : 5 ≤ n) : 
    9 * (∑ k ∈ range n, k^2 / n) ≥ (n - 1) * (n - 2) := by
  have h1 := S_lower_bound n hn
  have h2 := S_sum_ge_target n hn
  omega

lemma A048153_le_n_mul_sub (n : ℕ) (hn : 5 ≤ n) : A048153 n ≤ n * (n - 1) / 2 := by
  have h_add := A048153_add_div_eq_sq n
  have h_sq := sum_range_sq n
  have h_ge := S_lower_bound_target n hn

  have h_B : 6 * n * ∑ k ∈ range n, k^2 / n = 6 * (n * ∑ k ∈ range n, k^2 / n) := by ring

  -- 6 * A048153 n + 6 * n * ∑ k^2 / n = 6 * ∑ k^2
  have h1 : 6 * A048153 n + 6 * (n * ∑ k ∈ range n, k^2 / n) = (n - 1) * n * (2 * n - 1) := by
    calc 6 * A048153 n + 6 * (n * ∑ k ∈ range n, k^2 / n) 
      _ = 6 * (A048153 n + n * ∑ k ∈ range n, k^2 / n) := by ring
      _ = 6 * ∑ k ∈ range n, k^2 := by rw [h_add]
      _ = (n - 1) * n * (2 * n - 1) := h_sq

  -- 18 * A048153 n + 18 * n * ∑ k^2 / n = 3 * (n - 1) * n * (2 * n - 1)
  have h1_mul : 18 * A048153 n + 18 * (n * ∑ k ∈ range n, k^2 / n) = 3 * (n - 1) * n * (2 * n - 1) := by
    calc 18 * A048153 n + 18 * (n * ∑ k ∈ range n, k^2 / n)
      _ = 3 * (6 * A048153 n + 6 * (n * ∑ k ∈ range n, k^2 / n)) := by ring
      _ = 3 * ((n - 1) * n * (2 * n - 1)) := by rw [h1]
      _ = 3 * (n - 1) * n * (2 * n - 1) := by ring

  -- 18 * n * ∑ k^2 / n ≥ 2 * n * (n - 1) * (n - 2)
  have h2 : 18 * (n * ∑ k ∈ range n, k^2 / n) ≥ 2 * n * (n - 1) * (n - 2) := by
    calc 18 * (n * ∑ k ∈ range n, k^2 / n) 
      _ = 2 * n * (9 * ∑ k ∈ range n, k^2 / n) := by ring
      _ ≥ 2 * n * ((n - 1) * (n - 2)) := Nat.mul_le_mul_left (2 * n) h_ge
      _ = 2 * n * (n - 1) * (n - 2) := by ring

  have h3 : 18 * A048153 n + 2 * n * (n - 1) * (n - 2) ≤ 3 * (n - 1) * n * (2 * n - 1) := by
    calc 18 * A048153 n + 2 * n * (n - 1) * (n - 2)
      _ ≤ 18 * A048153 n + 18 * (n * ∑ k ∈ range n, k^2 / n) := Nat.add_le_add_left h2 _
      _ = 3 * (n - 1) * n * (2 * n - 1) := h1_mul

  have h4 : 2 * n * (n - 1) * (n - 2) + 9 * n * (n - 1) ≥ 3 * (n - 1) * n * (2 * n - 1) := by
    rcases n with _ | _ | _ | _ | _ | n
    · omega
    · omega
    · omega
    · omega
    · omega
    · have h_sub1 : n + 5 - 1 = n + 4 := by omega
      have h_sub2 : n + 5 - 2 = n + 3 := by omega
      have h_sub3 : 2 * (n + 5) - 1 = 2 * n + 9 := by omega
      rw [h_sub1, h_sub2, h_sub3]
      ring

  have h5 : 18 * A048153 n ≤ 9 * n * (n - 1) := by
    omega

  have h_even : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have : k + k = 2 * k := by omega
      rw [this, mul_assoc]
      exact dvd_mul_right 2 _
    · have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this, mul_comm, mul_assoc]
      exact dvd_mul_right 2 _

  have h_cancel : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' h_even

  have h6 : 9 * n * (n - 1) = 18 * (n * (n - 1) / 2) := by
    calc 9 * n * (n - 1) = 9 * (n * (n - 1)) := by ring
      _ = 9 * (2 * (n * (n - 1) / 2)) := by rw [h_cancel]
      _ = 18 * (n * (n - 1) / 2) := by ring

  have h7 : 18 * A048153 n ≤ 18 * (n * (n - 1) / 2) := by
    omega

  exact Nat.le_of_mul_le_mul_left h7 (by omega)
