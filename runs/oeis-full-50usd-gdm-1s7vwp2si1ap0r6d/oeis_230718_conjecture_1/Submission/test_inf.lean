import FormalConjectures.Util.ProblemImports

open Finset Nat

lemma sum_ge_two_terms (n N k : ℕ) (hN : N ≥ 3) (hk2 : k ≤ N - 2) :
    (Ico k N).sum (fun i => i ^ n) ≥ (N - 1) ^ n + (N - 2) ^ n := by
  have hN2 : N = N - 2 + 2 := by omega
  rw [hN2]
  generalize hA : N - 2 = A
  have h_eq1 : A + 2 - 1 = A + 1 := by omega
  have h_eq2 : A + 2 - 2 = A := by omega
  rw [h_eq1, h_eq2]
  have h_le1 : k ≤ A + 1 := by omega
  have h_eq_succ : A + 2 = A + 1 + 1 := rfl
  rw [h_eq_succ]
  rw [sum_Ico_succ_top h_le1]
  have h_le2 : k ≤ A := by omega
  rw [sum_Ico_succ_top h_le2]
  omega

lemma mul_pow_sub_one_local (n N : ℕ) : (n * N ^ (n - 1)) * N = n * N ^ n := by
  by_cases hn : n = 0
  · subst hn; simp
  · have h1 : n - 1 + 1 = n := by omega
    have h2 : N ^ (n - 1) * N = N ^ n := by
      rw [← pow_succ, h1]
    rw [mul_assoc, h2]

lemma bernoulli_1_nat_strict (n N : ℕ) (hn : n ≥ 2) (hN : 2 ≤ N) : N ^ n < (N - 1) ^ n + n * N ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    -- n = 2
    have hN1 : N - 1 = N - 2 + 1 := by omega
    have hN_eq : N = N - 2 + 2 := by omega
    rw [hN1, hN_eq]
    generalize hA : N - 2 = A
    have h_eq_sub : A + 2 - 2 + 1 = A + 1 := by omega
    have h_eq_sub2 : 2 - 1 = 1 := by omega
    rw [h_eq_sub, h_eq_sub2]
    have h_eq : (A + 2) ^ 2 = A ^ 2 + 4 * A + 4 := by ring
    have h_eq2 : (A + 1) ^ 2 + 2 * (A + 2) ^ 1 = A ^ 2 + 4 * A + 5 := by ring
    rw [h_eq, h_eq2]
    omega
  | succ n hn ih =>
    -- Multiply ih by N
    have h_pos_N : 0 < N := by omega
    have h_ih_mul : N ^ n * N < ((N - 1) ^ n + n * N ^ (n - 1)) * N := Nat.mul_lt_mul_of_pos_right ih h_pos_N
    have h_target : N ^ (n + 1) < (N - 1) ^ (n + 1) + (n + 1) * N ^ n := by
      rw [pow_succ]
      refine lt_of_lt_of_le h_ih_mul ?_
      have h_split : ((N - 1) ^ n + n * N ^ (n - 1)) * N = (N - 1) ^ (n + 1) + (N - 1) ^ n + n * N ^ n := by
        rw [add_mul]
        rw [mul_pow_sub_one_local]
        have h_N_eq : N = (N - 1) + 1 := by omega
        rw [h_N_eq]
        have h_sub : (N - 1) + 1 - 1 = N - 1 := by omega
        rw [h_sub]
        rw [mul_add, mul_one, ← pow_succ]
      rw [h_split]
      have h_add_mul : (n + 1) * N ^ n = n * N ^ n + N ^ n := by
        rw [add_mul, one_mul]
      rw [h_add_mul]
      have h_pow_le : (N - 1) ^ n ≤ N ^ n := Nat.pow_le_pow_left (by omega) n
      omega
    exact h_target

lemma mul_pow_sub_one_local_2 (n N : ℕ) : (2 * n * N ^ (n - 1)) * N = 2 * n * N ^ n := by
  calc
    (2 * n * N ^ (n - 1)) * N = 2 * ((n * N ^ (n - 1)) * N) := by ring
    _ = 2 * (n * N ^ n) := by rw [mul_pow_sub_one_local]
    _ = 2 * n * N ^ n := by ring

lemma bernoulli_2_nat (n N : ℕ) (hN : 2 ≤ N) : N ^ n ≤ (N - 2) ^ n + 2 * n * N ^ (n - 1) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h_ih_mul : N ^ n * N ≤ ((N - 2) ^ n + 2 * n * N ^ (n - 1)) * N := Nat.mul_le_mul_right N ih
    have h_target : N ^ (n + 1) ≤ (N - 2) ^ (n + 1) + 2 * (n + 1) * N ^ n := by
      rw [pow_succ]
      refine le_trans h_ih_mul ?_
      have h_split : ((N - 2) ^ n + 2 * n * N ^ (n - 1)) * N = (N - 2) ^ (n + 1) + 2 * (N - 2) ^ n + 2 * n * N ^ n := by
        rw [add_mul]
        rw [mul_pow_sub_one_local_2]
        have h_N_eq : N = (N - 2) + 2 := by omega
        rw [h_N_eq]
        have h_sub : (N - 2) + 2 - 2 = N - 2 := by omega
        rw [h_sub]
        rw [mul_add, mul_comm _ 2, ← pow_succ]
      rw [h_split]
      have h_add_mul : 2 * (n + 1) * N ^ n = 2 * n * N ^ n + 2 * N ^ n := by
        ring
      rw [h_add_mul]
      have h_pow_le : (N - 2) ^ n ≤ N ^ n := Nat.pow_le_pow_left (by omega) n
      omega
    exact h_target

lemma bernoulli_3_nat (n N : ℕ) (hn : n ≥ 2) (hN : N ≥ 3 * n) : N ^ n < (N - 1) ^ n + (N - 2) ^ n := by
  have hN2 : 2 ≤ N := by omega
  have h_strict : N ^ n < (N - 1) ^ n + n * N ^ (n - 1) := bernoulli_1_nat_strict n N hn hN2
  have h_le : N ^ n ≤ (N - 2) ^ n + 2 * n * N ^ (n - 1) := bernoulli_2_nat n N hN2
  have h_sum : N ^ n + N ^ n < (N - 1) ^ n + n * N ^ (n - 1) + ((N - 2) ^ n + 2 * n * N ^ (n - 1)) := Nat.add_lt_add_of_lt_of_le h_strict h_le
  have h_pos : 0 < n := by omega
  have h_pow_sub : N ^ (n - 1) * N = N ^ n := by
    have h1 : n - 1 + 1 = n := by omega
    rw [← pow_succ, h1]
  have h_bound : 3 * n * N ^ (n - 1) ≤ N ^ n := by
    rw [← h_pow_sub]
    have h_le_N : 3 * n ≤ N := hN
    have h_step := Nat.mul_le_mul_right (N ^ (n - 1)) h_le_N
    have h_comm : N * N ^ (n - 1) = N ^ (n - 1) * N := by ring
    rw [h_comm] at h_step
    exact h_step
  have h_sum2 : (N - 1) ^ n + n * N ^ (n - 1) + ((N - 2) ^ n + 2 * n * N ^ (n - 1)) = (N - 1) ^ n + (N - 2) ^ n + 3 * n * N ^ (n - 1) := by ring
  rw [h_sum2] at h_sum
  have h_add : (N - 1) ^ n + (N - 2) ^ n + 3 * n * N ^ (n - 1) ≤ (N - 1) ^ n + (N - 2) ^ n + N ^ n := by omega
  have h_final : N ^ n + N ^ n < (N - 1) ^ n + (N - 2) ^ n + N ^ n := lt_of_lt_of_le h_sum h_add
  omega

lemma sum_gt_N_pow (n N k : ℕ) (hn : n ≥ 2) (hN : N ≥ 3 * n) (hk2 : k ≤ N - 2) :
    (Ico k N).sum (fun i => i ^ n) > N ^ n := by
  have h_ge : (Ico k N).sum (fun i => i ^ n) ≥ (N - 1) ^ n + (N - 2) ^ n := sum_ge_two_terms n N k (by omega) hk2
  have h_gt : (N - 1) ^ n + (N - 2) ^ n > N ^ n := bernoulli_3_nat n N hn hN
  exact lt_of_lt_of_le h_gt h_ge

lemma N_lt_3n (n N k : ℕ) (hn : n ≥ 2) (hk2 : k ≤ N - 2) (h_sum : (Ico k N).sum (fun i => i ^ n) = N ^ n) : N < 3 * n := by
  by_contra h_ge
  push_neg at h_ge
  have h_gt : (Ico k N).sum (fun i => i ^ n) > N ^ n := sum_gt_N_pow n N k hn h_ge hk2
  omega

lemma lower_bound (n N : ℕ) : N ^ n + n * N ^ (n - 1) ≤ (N + 1) ^ n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h_ih_mul : (N ^ n + n * N ^ (n - 1)) * (N + 1) ≤ (N + 1) ^ n * (N + 1) := Nat.mul_le_mul_right (N + 1) ih
    have h_target : N ^ (n + 1) + (n + 1) * N ^ n ≤ (N + 1) ^ (n + 1) := by
      rw [pow_succ]
      refine le_trans ?_ h_ih_mul
      have h_split : (N ^ n + n * N ^ (n - 1)) * (N + 1) = N ^ n * N + (n + 1) * N ^ n + n * N ^ (n - 1) := by
        rw [add_mul, mul_add, mul_add, mul_one, mul_one]
        rw [mul_pow_sub_one_local]
        ring
      rw [h_split]
      omega
    exact h_target

lemma sum_lt_N_pow (n : ℕ) (hn : n ≥ 1) (N : ℕ) (hN1 : 1 ≤ N) (hN2 : N ≤ n + 1) :
    (range N).sum (fun i => i ^ n) < N ^ n := by
  induction N, hN1 using Nat.le_induction with
  | base =>
    simp
    omega
  | succ N hN1 ih =>
    have h_le_n : N ≤ n := by omega
    have h_sum_succ : (range (N + 1)).sum (fun i => i ^ n) = (range N).sum (fun i => i ^ n) + N ^ n := by
      exact sum_range_succ (fun i => i ^ n) N
    rw [h_sum_succ]
    have ih_val : (range N).sum (fun i => i ^ n) < N ^ n := ih (by omega)
    have h_lt : (range N).sum (fun i => i ^ n) + N ^ n < 2 * N ^ n := by omega
    refine lt_of_lt_of_le h_lt ?_
    -- We want to prove 2 * N ^ n ≤ (N + 1) ^ n
    -- By lower_bound: N ^ n + n * N ^ (n - 1) ≤ (N + 1) ^ n
    -- And since N ≤ n: N ^ n ≤ n * N ^ (n - 1)
    have h_lower := lower_bound n N
    have h_pow_eq : N ^ n = N ^ (n - 1) * N := by
      have h1 : n - 1 + 1 = n := by omega
      rw [← pow_succ, h1]
    have h_le_mul : N ^ n ≤ n * N ^ (n - 1) := by
      rw [h_pow_eq]
      have h_step := Nat.mul_le_mul_left (N ^ (n - 1)) h_le_n
      have h_comm2 : N ^ (n - 1) * n = n * N ^ (n - 1) := by ring
      rw [h_comm2] at h_step
      exact h_step
    omega


lemma sum_le_sum_range (n N k : ℕ) (hk : k ≤ N) :
    (Ico k N).sum (fun i => i ^ n) ≤ (range N).sum (fun i => i ^ n) := by
  rw [range_eq_Ico]
  have h0 : 0 ≤ k := by omega
  rw [← sum_Ico_consecutive _ h0 hk]
  omega

lemma N_gt_n_plus_one (n N k : ℕ) (hn : n ≥ 1) (hk1 : 1 ≤ k) (hk2 : k ≤ N - 2)
    (h_sum : (Ico k N).sum (fun i => i ^ n) = N ^ n) : N > n + 1 := by
  by_contra h_le
  push_neg at h_le
  have hN1 : 1 ≤ N := by omega
  have h_sum_le : (Ico k N).sum (fun i => i ^ n) ≤ (range N).sum (fun i => i ^ n) := by
    refine sum_le_sum_range n N k (by omega)
  have h_lt : (range N).sum (fun i => i ^ n) < N ^ n := sum_lt_N_pow n hn N hN1 h_le
  omega








