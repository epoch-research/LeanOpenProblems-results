import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Choose.Sum

open Finset Nat

/--
A230718: Smallest $n$-th power equal to a sum of some consecutive, immediately preceding, positive $n$-th powers, or 0 if none.
$a(n)$ is the smallest solution to $k^n + (k+1)^n + \dots + (k+m)^n = (k+m+1)^n$ with $k > 0$ and $m > 0$, or $0$ if none.
-/
noncomputable def A230718 (n : ℕ) : ℕ :=
  if n = 0 then 1 else
  -- Let $N = k+m+1$
  let P (N : ℕ) : Prop :=
    N ≥ 3 ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧
    (Finset.Ico k N).sum (fun i => i ^ n) = N ^ n

  let Solutions : Set ℕ := { N : ℕ | P N }

  let N_min := sInf Solutions

  -- If Solutions is empty, N_min = 0 (since ℕ is OrderBot), so we return 0.
  -- Otherwise, N_min ≥ 3, and we return N_min ^ n.
  if N_min = 0 then 0 else N_min ^ n

/-- oeis_230718_conjecture_1: Is a(n) $\ne 0$ for any $n > 3$?
The conjecture is that $a(n) = 0$ for all $n > 3$.
The Erdos-Moser equation is the case $k = 1$. They conjecture that the only solution is $m = n = 1$.
Any counterexample would be a case of $a(n) > 0$ with $n > 3$.
And such a case with $k = 1$ would be a counterexample to the Erdos-Moser conjecture. -/
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

lemma bernoulli_1_nat_le (n N : ℕ) (hn : n ≥ 1) (hN : 1 ≤ N) : N ^ n ≤ (N - 1) ^ n + n * N ^ (n - 1) := by
  by_cases hn2 : n ≥ 2
  · by_cases hN2 : 2 ≤ N
    · exact le_of_lt (bernoulli_1_nat_strict n N hn2 hN2)
    · have hN1 : N = 1 := by omega
      subst hN1
      have h0 : 0 < n := by omega
      rw [Nat.zero_pow h0]
      simp
      omega
  · have hn1 : n = 1 := by omega
    subst hn1
    simp
    omega


lemma sub_one_pow_le (n : ℕ) (hn : n ≥ 2) (A : ℕ) (hA : 1 ≤ A) :
    (A - 1) ^ n + n * A ^ (n - 1) ≤ A ^ n + (n.choose 2) * A ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base =>
    generalize h_X : A - 1 = X
    have hA1 : A = X + 1 := by omega
    rw [hA1]
    have h_base1 : 2 - 1 = 1 := rfl
    have h_base2 : 2 - 2 = 0 := rfl
    rw [h_base1, h_base2]
    simp only [Nat.choose_self, mul_one, pow_zero, pow_one, Nat.sub_self]
    have h_ring : X ^ 2 + 2 * (X + 1) = (X + 1) ^ 2 + 1 := by ring
    rw [h_ring]
  | succ n hn ih =>
    have h_sub1 : n + 1 - 1 = n := by omega
    have h_sub2 : n + 1 - 2 = n - 1 := by omega
    rw [h_sub1, h_sub2]
    have h_ih_mul : ((A - 1) ^ n + n * A ^ (n - 1)) * A ≤ (A ^ n + (n.choose 2) * A ^ (n - 2)) * A := Nat.mul_le_mul_right A ih
    simp only [add_mul] at h_ih_mul
    have h_assoc1 : n * A ^ (n - 1) * A = n * (A ^ (n - 1) * A) := by ring
    rw [h_assoc1] at h_ih_mul
    have h_pow1 : A ^ (n - 1) * A = A ^ n := by
      rw [← pow_succ]
      have h_exp : n - 1 + 1 = n := by omega
      rw [h_exp]
    rw [h_pow1] at h_ih_mul
    have h_assoc2 : (n.choose 2) * A ^ (n - 2) * A = (n.choose 2) * (A ^ (n - 2) * A) := by ring
    rw [h_assoc2] at h_ih_mul
    have h_pow2 : A ^ (n - 2) * A = A ^ (n - 1) := by
      rw [← pow_succ]
      have h_exp : n - 2 + 1 = n - 1 := by omega
      rw [h_exp]
    rw [h_pow2] at h_ih_mul
    have h_pow_succ_A : A ^ n * A = A ^ (n + 1) := by rw [← pow_succ]
    rw [h_pow_succ_A] at h_ih_mul
    have h_A_eq : A = A - 1 + 1 := by omega
    have h_split : (A - 1) ^ n * A = (A - 1) ^ (n + 1) + (A - 1) ^ n := by
      conv => lhs; enter [2]; rw [h_A_eq]
      rw [mul_add, mul_one, ← pow_succ]
    rw [h_split] at h_ih_mul
    have h_bern : A ^ n ≤ (A - 1) ^ n + n * A ^ (n - 1) := bernoulli_1_nat_le n A (by omega) hA
    have h_add := Nat.add_le_add h_ih_mul h_bern
    have h_choose_eq : (n + 1).choose 2 = n.choose 2 + n := by
      have h_succ_succ : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
      rw [h_succ_succ, Nat.choose_one_right, add_comm]
    have h_goal_rewrite1 : (n + 1) * A ^ n = n * A ^ n + A ^ n := by ring
    have h_goal_rewrite2 : (n.choose 2 + n) * A ^ (n - 1) = n.choose 2 * A ^ (n - 1) + n * A ^ (n - 1) := by ring
    rw [h_goal_rewrite1, h_choose_eq, h_goal_rewrite2]
    omega



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


lemma mul_pow_sub_one_local_3 (n N : ℕ) : (3 * n * N ^ (n - 1)) * N = 3 * n * N ^ n := by
  calc
    (3 * n * N ^ (n - 1)) * N = 3 * ((n * N ^ (n - 1)) * N) := by ring
    _ = 3 * (n * N ^ n) := by rw [mul_pow_sub_one_local]
    _ = 3 * n * N ^ n := by ring

lemma bernoulli_3_nat_le (n N : ℕ) (hN : 3 ≤ N) : N ^ n ≤ (N - 3) ^ n + 3 * n * N ^ (n - 1) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h_ih_mul : N ^ n * N ≤ ((N - 3) ^ n + 3 * n * N ^ (n - 1)) * N := Nat.mul_le_mul_right N ih
    have h_target : N ^ (n + 1) ≤ (N - 3) ^ (n + 1) + 3 * (n + 1) * N ^ n := by
      rw [pow_succ]
      refine le_trans h_ih_mul ?_
      have h_split : ((N - 3) ^ n + 3 * n * N ^ (n - 1)) * N = (N - 3) ^ (n + 1) + 3 * (N - 3) ^ n + 3 * n * N ^ n := by
        rw [add_mul]
        rw [mul_pow_sub_one_local_3]
        have h_N_eq : N = (N - 3) + 3 := by omega
        rw [h_N_eq]
        have h_sub : (N - 3) + 3 - 3 = N - 3 := by omega
        rw [h_sub]
        rw [mul_add, mul_comm _ 3, ← pow_succ]
      rw [h_split]
      have h_add_mul : 3 * (n + 1) * N ^ n = 3 * n * N ^ n + 3 * N ^ n := by
        ring
      rw [h_add_mul]
      have h_pow_le : (N - 3) ^ n ≤ N ^ n := Nat.pow_le_pow_left (by omega) n
      omega
    exact h_target

lemma sum_three_gt_N_pow (n N : ℕ) (hn : n ≥ 2) (hN : N ≥ 2 * n) :
    (N - 1) ^ n + (N - 2) ^ n + (N - 3) ^ n > N ^ n := by
  have hN3 : 3 ≤ N := by omega
  have h1 := bernoulli_1_nat_strict n N hn (by omega)
  have h2 := bernoulli_2_nat n N (by omega)
  have h3 := bernoulli_3_nat_le n N hN3
  have h_sum : N ^ n + N ^ n + N ^ n < (N - 1) ^ n + n * N ^ (n - 1) + ((N - 2) ^ n + 2 * n * N ^ (n - 1)) + ((N - 3) ^ n + 3 * n * N ^ (n - 1)) := by omega
  have h_pow_sub : N ^ (n - 1) * N = N ^ n := by
    have h_eq : n - 1 + 1 = n := by omega
    rw [← pow_succ, h_eq]
  have h_bound : 6 * n * N ^ (n - 1) ≤ 3 * N ^ n := by
    rw [← h_pow_sub]
    have h_le_N : 2 * n ≤ N := hN
    have h_step : 6 * n ≤ 3 * N := by omega
    calc
      6 * n * N ^ (n - 1) ≤ 3 * N * N ^ (n - 1) := Nat.mul_le_mul_right (N ^ (n - 1)) h_step
      _ = 3 * (N ^ (n - 1) * N) := by ring
  have h_ring_sum : (N - 1) ^ n + n * N ^ (n - 1) + ((N - 2) ^ n + 2 * n * N ^ (n - 1)) + ((N - 3) ^ n + 3 * n * N ^ (n - 1)) =
      (N - 1) ^ n + (N - 2) ^ n + (N - 3) ^ n + 6 * n * N ^ (n - 1) := by ring
  rw [h_ring_sum] at h_sum
  have h_add : (N - 1) ^ n + (N - 2) ^ n + (N - 3) ^ n + 6 * n * N ^ (n - 1) ≤ (N - 1) ^ n + (N - 2) ^ n + (N - 3) ^ n + 3 * N ^ n := by omega
  have h_final : N ^ n + N ^ n + N ^ n < (N - 1) ^ n + (N - 2) ^ n + (N - 3) ^ n + 3 * N ^ n := lt_of_lt_of_le h_sum h_add
  have h_sum_3 : N ^ n + N ^ n + N ^ n = 3 * N ^ n := by ring
  rw [h_sum_3] at h_final
  omega

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


lemma lower_bound_three_terms (n : ℕ) (hn : n ≥ 2) (N : ℕ) :
    (N + 1) ^ n + n * (N + 1) ^ (n - 1) + (n.choose 2) * (N + 1) ^ (n - 2) ≤ (N + 2) ^ n := by
  have h_add : N + 2 = 1 + (N + 1) := by omega
  rw [h_add]
  rw [add_pow 1 (N + 1) n]
  have hn1 : n = n - 1 + 1 := by omega
  have hn2 : n - 1 = n - 2 + 1 := by omega
  rw [hn1]
  rw [sum_range_succ']
  have h_f0 : 1 ^ 0 * (N + 1) ^ (n - 0) * (n.choose 0) = (N + 1) ^ n := by
    simp
  rw [hn2]
  rw [sum_range_succ']
  have h_f1 : 1 ^ (0 + 1) * (N + 1) ^ (n - (0 + 1)) * (n.choose (0 + 1)) = n * (N + 1) ^ (n - 1) := by
    simp
    ring
  rw [sum_range_succ']
  have h_f2 : 1 ^ (0 + 1 + 1) * (N + 1) ^ (n - (0 + 1 + 1)) * (n.choose (0 + 1 + 1)) = (n.choose 2) * (N + 1) ^ (n - 2) := by
    simp
    ring
  have h_n_eq : n - 2 + 1 + 1 = n := by omega
  rw [h_n_eq]
  simp only [Nat.cast_id]
  rw [h_f0, h_f1, h_f2]
  omega

lemma two_pow_le_succ_pow_1 (n : ℕ) (hn : n ≥ 9) :
    2 * (n + 1) ^ n ≤ (n + 1) ^ n + n * (n + 1) ^ (n - 1) + (n.choose 2) * (n + 1) ^ (n - 2) := by
  have hn2 : 2 ≤ n := by omega
  rw [Nat.choose_two_right n]
  have h_pow1 : (n + 1) ^ n = (n + 1) ^ (n - 2) * (n + 1) ^ 2 := by
    have h1 : n = n - 2 + 2 := by omega
    conv => lhs; rhs; rw [h1]
    rw [pow_add]
  have h_pow2 : n * (n + 1) ^ (n - 1) = (n + 1) ^ (n - 2) * (n * (n + 1)) := by
    have h1 : n - 1 = n - 2 + 1 := by omega
    rw [h1, pow_add]
    ring
  have h_pow3 : (n * (n - 1) / 2) * (n + 1) ^ (n - 2) = (n + 1) ^ (n - 2) * (n * (n - 1) / 2) := by
    ring
  rw [h_pow1, h_pow2, h_pow3]
  have h_lhs : 2 * ((n + 1) ^ (n - 2) * (n + 1) ^ 2) = (n + 1) ^ (n - 2) * (2 * (n + 1) ^ 2) := by ring
  rw [h_lhs]
  rw [← mul_add, ← mul_add]
  refine Nat.mul_le_mul_left _ ?_
  have h_even : Even (n * (n - 1)) := by
    cases Nat.even_or_odd n with
    | inl h => exact Even.mul_right h (n - 1)
    | inr h =>
      rcases h with ⟨k, rfl⟩
      have : 2 * k + 1 - 1 = 2 * k := by omega
      have h_even_sub : Even (2 * k + 1 - 1) := by
        rw [this]
        use k
        ring
      exact Even.mul_left h_even_sub (2 * k + 1)
  have h_div : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' (Even.two_dvd h_even)
  have h_eq1 : (n + 1) ^ 2 = n^2 + 2 * n + 1 := by ring
  have h_eq2 : n * (n + 1) = n^2 + n := by ring
  have h_mul_le : 2 * (2 * (n + 1) ^ 2) ≤ 2 * ((n + 1) ^ 2 + n * (n + 1) + n * (n - 1) / 2) := by
    clear h_pow1 h_pow2 h_pow3 h_lhs hn2
    have h_dist : 2 * ((n + 1) ^ 2 + n * (n + 1) + n * (n - 1) / 2) = 2 * (n + 1) ^ 2 + 2 * (n * (n + 1)) + 2 * (n * (n - 1) / 2) := by ring
    rw [h_dist]
    clear h_dist
    rw [h_div]
    clear h_div h_even
    rw [h_eq1, h_eq2]
    clear h_eq1 h_eq2
    have h_sub : n * (n - 1) = n^2 - n := by
      rw [Nat.mul_sub_left_distrib, mul_one, ← pow_two]
    rw [h_sub]
    clear h_sub
    generalize h_X : n^2 = X
    have h_bound : 2 * n + 2 ≤ X - n := by
      rw [← h_X]
      have h_quad : 3 * n + 2 ≤ n^2 := by
        rw [pow_two]
        calc
          3 * n + 2 ≤ 3 * n + n - 2 := by omega
          _ = 4 * n - 2 := by omega
          _ ≤ n * n := by
            have h_le : 4 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
            omega
      omega
    generalize hY : X - n = Y
    rw [hY] at h_bound
    clear h_X
    omega
  clear h_pow1 h_pow2 h_pow3 h_lhs hn2 h_even h_div h_eq1 h_eq2
  omega

lemma two_pow_le_succ_pow_2 (n : ℕ) (hn : n ≥ 9) :
    2 * (n + 2) ^ n ≤ (n + 2) ^ n + n * (n + 2) ^ (n - 1) + (n.choose 2) * (n + 2) ^ (n - 2) := by
  have hn2 : 2 ≤ n := by omega
  rw [Nat.choose_two_right n]
  have h_pow1 : (n + 2) ^ n = (n + 2) ^ (n - 2) * (n + 2) ^ 2 := by
    have h1 : n = n - 2 + 2 := by omega
    conv => lhs; rhs; rw [h1]
    rw [pow_add]
  have h_pow2 : n * (n + 2) ^ (n - 1) = (n + 2) ^ (n - 2) * (n * (n + 2)) := by
    have h1 : n - 1 = n - 2 + 1 := by omega
    rw [h1, pow_add]
    ring
  have h_pow3 : (n * (n - 1) / 2) * (n + 2) ^ (n - 2) = (n + 2) ^ (n - 2) * (n * (n - 1) / 2) := by
    ring
  rw [h_pow1, h_pow2, h_pow3]
  have h_lhs : 2 * ((n + 2) ^ (n - 2) * (n + 2) ^ 2) = (n + 2) ^ (n - 2) * (2 * (n + 2) ^ 2) := by ring
  rw [h_lhs]
  rw [← mul_add, ← mul_add]
  refine Nat.mul_le_mul_left _ ?_
  have h_even : Even (n * (n - 1)) := by
    cases Nat.even_or_odd n with
    | inl h => exact Even.mul_right h (n - 1)
    | inr h =>
      rcases h with ⟨k, rfl⟩
      have : 2 * k + 1 - 1 = 2 * k := by omega
      have h_even_sub : Even (2 * k + 1 - 1) := by
        rw [this]
        use k
        ring
      exact Even.mul_left h_even_sub (2 * k + 1)
  have h_div : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' (Even.two_dvd h_even)
  have h_eq1 : (n + 2) ^ 2 = n^2 + 4 * n + 4 := by ring
  have h_eq2 : n * (n + 2) = n^2 + 2 * n := by ring
  have h_mul_le : 2 * (2 * (n + 2) ^ 2) ≤ 2 * ((n + 2) ^ 2 + n * (n + 2) + n * (n - 1) / 2) := by
    clear h_pow1 h_pow2 h_pow3 h_lhs hn2
    have h_dist : 2 * ((n + 2) ^ 2 + n * (n + 2) + n * (n - 1) / 2) = 2 * (n + 2) ^ 2 + 2 * (n * (n + 2)) + 2 * (n * (n - 1) / 2) := by ring
    rw [h_dist]
    clear h_dist
    rw [h_div]
    clear h_div h_even
    rw [h_eq1, h_eq2]
    clear h_eq1 h_eq2
    have h_sub : n * (n - 1) = n^2 - n := by
      rw [Nat.mul_sub_left_distrib, mul_one, ← pow_two]
    rw [h_sub]
    clear h_sub
    generalize h_X : n^2 = X
    have h_bound : 4 * n + 8 ≤ X - n := by
      rw [← h_X]
      have h_quad : 5 * n + 8 ≤ n^2 := by
        rw [pow_two]
        calc
          5 * n + 8 ≤ 5 * n + 3 * n - 10 := by omega
          _ = 8 * n - 10 := by omega
          _ ≤ n * n := by
            have h_le : 8 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
            omega
      omega
    generalize hY : X - n = Y
    rw [hY] at h_bound
    clear h_X
    omega
  clear h_pow1 h_pow2 h_pow3 h_lhs hn2 h_even h_div h_eq1 h_eq2
  omega

lemma two_pow_le_succ_pow_3 (n : ℕ) (hn : n ≥ 9) :
    2 * (n + 3) ^ n ≤ (n + 3) ^ n + n * (n + 3) ^ (n - 1) + (n.choose 2) * (n + 3) ^ (n - 2) := by
  have hn2 : 2 ≤ n := by omega
  rw [Nat.choose_two_right n]
  have h_pow1 : (n + 3) ^ n = (n + 3) ^ (n - 2) * (n + 3) ^ 2 := by
    have h1 : n = n - 2 + 2 := by omega
    conv => lhs; rhs; rw [h1]
    rw [pow_add]
  have h_pow2 : n * (n + 3) ^ (n - 1) = (n + 3) ^ (n - 2) * (n * (n + 3)) := by
    have h1 : n - 1 = n - 2 + 1 := by omega
    rw [h1, pow_add]
    ring
  have h_pow3 : (n * (n - 1) / 2) * (n + 3) ^ (n - 2) = (n + 3) ^ (n - 2) * (n * (n - 1) / 2) := by
    ring
  rw [h_pow1, h_pow2, h_pow3]
  have h_lhs : 2 * ((n + 3) ^ (n - 2) * (n + 3) ^ 2) = (n + 3) ^ (n - 2) * (2 * (n + 3) ^ 2) := by ring
  rw [h_lhs]
  rw [← mul_add, ← mul_add]
  refine Nat.mul_le_mul_left _ ?_
  have h_even : Even (n * (n - 1)) := by
    cases Nat.even_or_odd n with
    | inl h => exact Even.mul_right h (n - 1)
    | inr h =>
      rcases h with ⟨k, rfl⟩
      have : 2 * k + 1 - 1 = 2 * k := by omega
      have h_even_sub : Even (2 * k + 1 - 1) := by
        rw [this]
        use k
        ring
      exact Even.mul_left h_even_sub (2 * k + 1)
  have h_div : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' (Even.two_dvd h_even)
  have h_eq1 : (n + 3) ^ 2 = n^2 + 6 * n + 9 := by ring
  have h_eq2 : n * (n + 3) = n^2 + 3 * n := by ring
  have h_mul_le : 2 * (2 * (n + 3) ^ 2) ≤ 2 * ((n + 3) ^ 2 + n * (n + 3) + n * (n - 1) / 2) := by
    clear h_pow1 h_pow2 h_pow3 h_lhs hn2
    have h_dist : 2 * ((n + 3) ^ 2 + n * (n + 3) + n * (n - 1) / 2) = 2 * (n + 3) ^ 2 + 2 * (n * (n + 3)) + 2 * (n * (n - 1) / 2) := by ring
    rw [h_dist]
    clear h_dist
    rw [h_div]
    clear h_div h_even
    rw [h_eq1, h_eq2]
    clear h_eq1 h_eq2
    have h_sub : n * (n - 1) = n^2 - n := by
      rw [Nat.mul_sub_left_distrib, mul_one, ← pow_two]
    rw [h_sub]
    clear h_sub
    generalize h_X : n^2 = X
    have h_bound : 6 * n + 18 ≤ X - n := by
      rw [← h_X]
      have h_quad : 7 * n + 18 ≤ n^2 := by
        rw [pow_two]
        calc
          7 * n + 18 ≤ 7 * n + 2 * n := by omega
          _ = 9 * n := by ring
          _ ≤ n * n := by
            have h_le : 9 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
            omega
      omega
    generalize hY : X - n = Y
    rw [hY] at h_bound
    clear h_X
    omega
  clear h_pow1 h_pow2 h_pow3 h_lhs hn2 h_even h_div h_eq1 h_eq2
  omega

lemma sum_lt_N_pow_n_plus_two (n : ℕ) (hn : n ≥ 9) : (range (n + 2)).sum (fun i => i ^ n) < (n + 2) ^ n := by
  have h_sum : (range (n + 2)).sum (fun i => i ^ n) = (range (n + 1)).sum (fun i => i ^ n) + (n + 1) ^ n := by
    exact sum_range_succ (fun i => i ^ n) (n + 1)
  rw [h_sum]
  have h_lt : (range (n + 1)).sum (fun i => i ^ n) < (n + 1) ^ n := by
    refine sum_lt_N_pow n (by omega) (n + 1) (by omega) (by omega)
  have h_le : 2 * (n + 1) ^ n ≤ (n + 2) ^ n := by
    have h_le1 := two_pow_le_succ_pow_1 n hn
    have h_le2 := lower_bound_three_terms n (by omega) n
    exact le_trans h_le1 h_le2
  omega

lemma sum_lt_N_pow_n_plus_three (n : ℕ) (hn : n ≥ 9) : (range (n + 3)).sum (fun i => i ^ n) < (n + 3) ^ n := by
  have h_sum : (range (n + 3)).sum (fun i => i ^ n) = (range (n + 2)).sum (fun i => i ^ n) + (n + 2) ^ n := by
    exact sum_range_succ (fun i => i ^ n) (n + 2)
  rw [h_sum]
  have h_lt : (range (n + 2)).sum (fun i => i ^ n) < (n + 2) ^ n := sum_lt_N_pow_n_plus_two n hn
  have h_le : 2 * (n + 2) ^ n ≤ (n + 3) ^ n := by
    have h_le1 := two_pow_le_succ_pow_2 n hn
    have h_le2 := lower_bound_three_terms n (by omega) (n + 1)
    exact le_trans h_le1 h_le2
  omega

lemma sum_lt_N_pow_n_plus_four (n : ℕ) (hn : n ≥ 9) : (range (n + 4)).sum (fun i => i ^ n) < (n + 4) ^ n := by
  have h_sum : (range (n + 4)).sum (fun i => i ^ n) = (range (n + 3)).sum (fun i => i ^ n) + (n + 3) ^ n := by
    exact sum_range_succ (fun i => i ^ n) (n + 3)
  rw [h_sum]
  have h_lt : (range (n + 3)).sum (fun i => i ^ n) < (n + 3) ^ n := sum_lt_N_pow_n_plus_three n hn
  have h_le : 2 * (n + 3) ^ n ≤ (n + 4) ^ n := by
    have h_le1 := two_pow_le_succ_pow_3 n hn
    have h_le2 := lower_bound_three_terms n (by omega) (n + 2)
    exact le_trans h_le1 h_le2
  omega


lemma lemma8_pow_le_1_6 (n N : ℕ) (hn : n ≥ 1) (hN1 : 2 ≤ N) (hN2 : N ≤ 16 * n / 10) :
    8 * (N - 2) ^ n ≤ 5 * (N - 1) ^ n := by
  have h_lower := lower_bound n (N - 2)
  have h_eq_sub : N - 2 + 1 = N - 1 := by omega
  rw [h_eq_sub] at h_lower
  have h_le_N1 : 3 * (N - 2) ≤ 5 * n := by omega
  have h_pow : (N - 2) ^ n = (N - 2) ^ (n - 1) * (N - 2) := by
    have h_eq : n = n - 1 + 1 := by omega
    conv => lhs; rw [h_eq]
    rw [pow_succ]
  have h_le_mul : 3 * (N - 2) ^ n ≤ 5 * (n * (N - 2) ^ (n - 1)) := by
    rw [h_pow]
    have h_step := Nat.mul_le_mul_left ((N - 2) ^ (n - 1)) h_le_N1
    have h_comm : (N - 2) ^ (n - 1) * (5 * n) = 5 * (n * (N - 2) ^ (n - 1)) := by ring
    rw [h_comm] at h_step
    have h_ring_eq : 3 * ((N - 2) ^ (n - 1) * (N - 2)) = (N - 2) ^ (n - 1) * (3 * (N - 2)) := by ring
    rw [h_ring_eq]
    exact h_step
  rw [h_pow] at h_lower
  rw [h_pow]
  omega

lemma lemma13_pow_le_1_6 (n N : ℕ) (hn : n ≥ 1) (hN1 : 2 ≤ N) (hN2 : N ≤ 16 * n / 10) :
    13 * (N - 1) ^ n < 8 * N ^ n := by
  have h_lower := lower_bound n (N - 1)
  have h_eq_sub2 : N - 1 + 1 = N := by omega
  rw [h_eq_sub2] at h_lower
  have h_le_N1 : 5 * (N - 1) < 8 * n := by omega
  have h_pow : (N - 1) ^ n = (N - 1) ^ (n - 1) * (N - 1) := by
    have h_eq : n = n - 1 + 1 := by omega
    conv => lhs; rw [h_eq]
    rw [pow_succ]
  have h_pos : 0 < (N - 1) ^ (n - 1) := Nat.pos_of_ne_zero (by
    have h_base : N - 1 ≠ 0 := by omega
    exact pow_ne_zero _ h_base)
  have h_le_mul : 5 * (N - 1) ^ n < 8 * (n * (N - 1) ^ (n - 1)) := by
    rw [h_pow]
    have h_step := Nat.mul_lt_mul_of_pos_right h_le_N1 h_pos
    have h_comm2 : 8 * n * (N - 1) ^ (n - 1) = 8 * (n * (N - 1) ^ (n - 1)) := by ring
    rw [h_comm2] at h_step
    have h_comm3 : 5 * (N - 1) * (N - 1) ^ (n - 1) = 5 * ((N - 1) ^ (n - 1) * (N - 1)) := by ring
    rw [h_comm3] at h_step
    exact h_step
  rw [h_pow] at h_lower
  rw [h_pow]
  omega

lemma sum_two_lt_N_pow_1_6 (n N : ℕ) (hn : n ≥ 1) (hN1 : 2 ≤ N) (hN2 : N ≤ 16 * n / 10) :
    (N - 1) ^ n + (N - 2) ^ n < N ^ n := by
  have h1 := lemma8_pow_le_1_6 n N hn hN1 hN2
  have h2 := lemma13_pow_le_1_6 n N hn hN1 hN2
  have h_sum : 104 * ((N - 1) ^ n + (N - 2) ^ n) < 104 * N ^ n := by
    calc
      104 * ((N - 1) ^ n + (N - 2) ^ n) = 104 * (N - 1) ^ n + 104 * (N - 2) ^ n := by ring
      _ ≤ 104 * (N - 1) ^ n + 65 * (N - 1) ^ n := by
        have h_mul : 13 * (8 * (N - 2) ^ n) ≤ 13 * (5 * (N - 1) ^ n) := Nat.mul_le_mul_left 13 h1
        have h_ring1 : 104 * (N - 2) ^ n = 13 * (8 * (N - 2) ^ n) := by ring
        have h_ring2 : 65 * (N - 1) ^ n = 13 * (5 * (N - 1) ^ n) := by ring
        rw [h_ring1, h_ring2]
        exact Nat.add_le_add_left h_mul _
      _ = 169 * (N - 1) ^ n := by ring
      _ < 104 * N ^ n := by
        have h_mul : 13 * (13 * (N - 1) ^ n) < 13 * (8 * N ^ n) := Nat.mul_lt_mul_of_pos_left h2 (by omega)
        have h_ring1 : 169 * (N - 1) ^ n = 13 * (13 * (N - 1) ^ n) := by ring
        have h_ring2 : 104 * N ^ n = 13 * (8 * N ^ n) := by ring
        rw [h_ring1, h_ring2]
        exact h_mul
  exact Nat.lt_of_mul_lt_mul_left h_sum


lemma sum_two_lt_N_pow_2n (n N : ℕ) (hn : n ≥ 2) (hN1 : n + 5 ≤ N) (hN2 : N ≤ 2 * n) :
    (N - 1) ^ n + (N - 2) ^ n < N ^ n := by
  have hA : 1 ≤ N - 1 := by omega
  have h_le1 := sub_one_pow_le n hn (N - 1) hA
  have h_le2 := lower_bound_three_terms n hn (N - 2)
  have h_sub_eq1 : N - 1 - 1 = N - 2 := by omega
  have h_sub_eq2 : N - 2 + 1 = N - 1 := by omega
  have h_sub_eq3 : N - 2 + 2 = N := by omega
  rw [h_sub_eq1] at h_le1
  rw [h_sub_eq2, h_sub_eq3] at h_le2
  have h_sum := Nat.add_le_add h_le1 h_le2
  have h_pow : (N - 1) ^ n = (N - 1) * (N - 1) ^ (n - 1) := by
    have h1 : n = n - 1 + 1 := by omega
    conv => lhs; rw [h1]
    rw [pow_succ]
    rw [mul_comm]
  have h_pos : 0 < (N - 1) ^ (n - 1) := Nat.pos_of_ne_zero (by
    have h_base : N - 1 ≠ 0 := by omega
    exact pow_ne_zero _ h_base)
  have h_lt_mul : (N - 1) ^ n < 2 * n * (N - 1) ^ (n - 1) := by
    rw [h_pow]
    have h_lt_N : N - 1 < 2 * n := by omega
    have h_step := Nat.mul_lt_mul_of_pos_right h_lt_N h_pos
    exact h_step
  have h_ring_sum : (N - 2) ^ n + n * (N - 1) ^ (n - 1) + ((N - 1) ^ n + n * (N - 1) ^ (n - 1) + n.choose 2 * (N - 1) ^ (n - 2)) =
      (N - 2) ^ n + 2 * n * (N - 1) ^ (n - 1) + ((N - 1) ^ n + n.choose 2 * (N - 1) ^ (n - 2)) := by ring
  rw [h_ring_sum] at h_sum
  have h_ring_sum2 : (N - 1) ^ n + n.choose 2 * (N - 1) ^ (n - 2) + N ^ n =
      N ^ n + ((N - 1) ^ n + n.choose 2 * (N - 1) ^ (n - 2)) := by ring
  rw [h_ring_sum2] at h_sum
  have h_final : (N - 2) ^ n + 2 * n * (N - 1) ^ (n - 1) ≤ N ^ n := by omega
  omega






lemma lemma2_pow_ge (n N : ℕ) (hn : n ≥ 2) (hN : N ≥ 2 * n) : N ^ n < 2 * (N - 1) ^ n := by
  have h_strict : N ^ n < (N - 1) ^ n + n * N ^ (n - 1) := bernoulli_1_nat_strict n N hn (by omega)
  have h_le_N : 2 * n ≤ N := hN
  have h_pow_eq : N ^ n = N ^ (n - 1) * N := by
    have h1 : n - 1 + 1 = n := by omega
    rw [← pow_succ, h1]
  have h_bound : 2 * n * N ^ (n - 1) ≤ N ^ n := by
    rw [h_pow_eq]
    have h_step := Nat.mul_le_mul_right (N ^ (n - 1)) h_le_N
    have h_comm : N * N ^ (n - 1) = N ^ (n - 1) * N := by ring
    rw [h_comm] at h_step
    exact h_step
  have h_mul_strict : 2 * N ^ n < 2 * ((N - 1) ^ n + n * N ^ (n - 1)) := Nat.mul_lt_mul_of_pos_left h_strict (by omega)
  have h_dist : 2 * ((N - 1) ^ n + n * N ^ (n - 1)) = 2 * (N - 1) ^ n + 2 * n * N ^ (n - 1) := by ring
  rw [h_dist] at h_mul_strict
  have h_final : 2 * N ^ n < 2 * (N - 1) ^ n + N ^ n := by omega
  omega


lemma no_sol_n_4 (N : ℕ) (hN1 : 6 ≤ N) (hN2 : N ≤ 11) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 4) = N ^ 4 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_5 (N : ℕ) (hN1 : 7 ≤ N) (hN2 : N ≤ 14) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 5) = N ^ 5 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_6 (N : ℕ) (hN1 : 8 ≤ N) (hN2 : N ≤ 17) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 6) = N ^ 6 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_7 (N : ℕ) (hN1 : 9 ≤ N) (hN2 : N ≤ 20) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 7) = N ^ 7 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_8 (N : ℕ) (hN1 : 10 ≤ N) (hN2 : N ≤ 23) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 8) = N ^ 8 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide


lemma no_sol_n_ge_201 (n N k : ℕ) (hn : n ≥ 201) (hN1 : n + 5 ≤ N) (hN2 : N < 3 * n) (hk1 : 1 ≤ k) (hk2 : k ≤ N - 2) :
    (Ico k N).sum (fun i => i ^ n) ≠ N ^ n := by
  sorry

theorem oeis_230718_conjecture_1 : ∀ (n : ℕ), n > 3 → A230718 n = 0 := by
  intro n hn
  unfold A230718
  have h_ne : n ≠ 0 := by omega
  simp only [h_ne, ↓reduceIte]
  have h_empty : { N : ℕ |
    N ≥ 3 ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧
    (Ico k N).sum (fun i => i ^ n) = N ^ n } = ∅ := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h_sol
    rcases h_sol with ⟨hN3, k, hk1, hk2, h_sum⟩
    have hn_ge2 : n ≥ 2 := by omega
    have h_lt : N < 3 * n := N_lt_3n n N k hn_ge2 hk2 h_sum
    have h_gt : N > n + 1 := N_gt_n_plus_one n N k (by omega) hk1 hk2 h_sum
    by_cases hn9 : n < 9
    · interval_cases n
      · exact no_sol_n_4 N (by omega) (by omega) ⟨k, hk1, hk2, h_sum⟩
      · exact no_sol_n_5 N (by omega) (by omega) ⟨k, hk1, hk2, h_sum⟩
      · exact no_sol_n_6 N (by omega) (by omega) ⟨k, hk1, hk2, h_sum⟩
      · exact no_sol_n_7 N (by omega) (by omega) ⟨k, hk1, hk2, h_sum⟩
      · exact no_sol_n_8 N (by omega) (by omega) ⟨k, hk1, hk2, h_sum⟩
    · push_neg at hn9
      by_cases h_cases : N ≤ n + 4
      · have h_sum_le : (Ico k N).sum (fun i => i ^ n) ≤ (range N).sum (fun i => i ^ n) :=
          sum_le_sum_range n N k (by omega)
        have h_lt_all : (range N).sum (fun i => i ^ n) < N ^ n := by
          have h_cases2 : N = n + 2 ∨ N = n + 3 ∨ N = n + 4 := by omega
          rcases h_cases2 with rfl | rfl | rfl
          · exact sum_lt_N_pow_n_plus_two n hn9
          · exact sum_lt_N_pow_n_plus_three n hn9
          · exact sum_lt_N_pow_n_plus_four n hn9
        omega
      · by_cases hn201 : n < 201
        · sorry
        · push_neg at hn201
          exact no_sol_n_ge_201 n N k hn201 (by omega) h_lt hk1 hk2 h_sum

  have h_min : sInf { N : ℕ |
    N ≥ 3 ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧
    (Ico k N).sum (fun i => i ^ n) = N ^ n } = 0 := by
    rw [h_empty]
    exact Nat.sInf_empty
  rw [h_min]
  rfl
