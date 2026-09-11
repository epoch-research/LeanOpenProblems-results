import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

open scoped Nat.Prime

/--
A238585: Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n)-1)^2$ prime.
(where $\text{prime}(i)$ is the $i$-th prime number, 1-indexed).
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0


/-! ### Verified finite part of the conjecture (all `n ≤ 44`).
The statements below are auxiliary and fully proved; they establish the conjecture's
claims on every case where it asserts something specific (the zero set `{1,2,3,6}` and the
twelve values of `n` with `a n = 1`). The general statement for all `n` is a Goldbach-type
open problem and remains `sorry`. -/

set_option maxRecDepth 100000

lemma nthP_0 : Nat.nth Nat.Prime 0 = 2 := by
  have h : Nat.count Nat.Prime 2 = 0 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_1 : Nat.nth Nat.Prime 1 = 3 := by
  have h : Nat.count Nat.Prime 3 = 1 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_2 : Nat.nth Nat.Prime 2 = 5 := by
  have h : Nat.count Nat.Prime 5 = 2 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_3 : Nat.nth Nat.Prime 3 = 7 := by
  have h : Nat.count Nat.Prime 7 = 3 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_4 : Nat.nth Nat.Prime 4 = 11 := by
  have h : Nat.count Nat.Prime 11 = 4 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_5 : Nat.nth Nat.Prime 5 = 13 := by
  have h : Nat.count Nat.Prime 13 = 5 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_6 : Nat.nth Nat.Prime 6 = 17 := by
  have h : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_7 : Nat.nth Nat.Prime 7 = 19 := by
  have h : Nat.count Nat.Prime 19 = 7 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_8 : Nat.nth Nat.Prime 8 = 23 := by
  have h : Nat.count Nat.Prime 23 = 8 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_9 : Nat.nth Nat.Prime 9 = 29 := by
  have h : Nat.count Nat.Prime 29 = 9 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_10 : Nat.nth Nat.Prime 10 = 31 := by
  have h : Nat.count Nat.Prime 31 = 10 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_11 : Nat.nth Nat.Prime 11 = 37 := by
  have h : Nat.count Nat.Prime 37 = 11 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_12 : Nat.nth Nat.Prime 12 = 41 := by
  have h : Nat.count Nat.Prime 41 = 12 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_13 : Nat.nth Nat.Prime 13 = 43 := by
  have h : Nat.count Nat.Prime 43 = 13 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_14 : Nat.nth Nat.Prime 14 = 47 := by
  have h : Nat.count Nat.Prime 47 = 14 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_15 : Nat.nth Nat.Prime 15 = 53 := by
  have h : Nat.count Nat.Prime 53 = 15 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_16 : Nat.nth Nat.Prime 16 = 59 := by
  have h : Nat.count Nat.Prime 59 = 16 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_17 : Nat.nth Nat.Prime 17 = 61 := by
  have h : Nat.count Nat.Prime 61 = 17 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_18 : Nat.nth Nat.Prime 18 = 67 := by
  have h : Nat.count Nat.Prime 67 = 18 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_19 : Nat.nth Nat.Prime 19 = 71 := by
  have h : Nat.count Nat.Prime 71 = 19 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_20 : Nat.nth Nat.Prime 20 = 73 := by
  have h : Nat.count Nat.Prime 73 = 20 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_21 : Nat.nth Nat.Prime 21 = 79 := by
  have h : Nat.count Nat.Prime 79 = 21 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_22 : Nat.nth Nat.Prime 22 = 83 := by
  have h : Nat.count Nat.Prime 83 = 22 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_23 : Nat.nth Nat.Prime 23 = 89 := by
  have h : Nat.count Nat.Prime 89 = 23 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_24 : Nat.nth Nat.Prime 24 = 97 := by
  have h : Nat.count Nat.Prime 97 = 24 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_25 : Nat.nth Nat.Prime 25 = 101 := by
  have h : Nat.count Nat.Prime 101 = 25 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_26 : Nat.nth Nat.Prime 26 = 103 := by
  have h : Nat.count Nat.Prime 103 = 26 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_27 : Nat.nth Nat.Prime 27 = 107 := by
  have h : Nat.count Nat.Prime 107 = 27 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_28 : Nat.nth Nat.Prime 28 = 109 := by
  have h : Nat.count Nat.Prime 109 = 28 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_29 : Nat.nth Nat.Prime 29 = 113 := by
  have h : Nat.count Nat.Prime 113 = 29 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_30 : Nat.nth Nat.Prime 30 = 127 := by
  have h : Nat.count Nat.Prime 127 = 30 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_31 : Nat.nth Nat.Prime 31 = 131 := by
  have h : Nat.count Nat.Prime 131 = 31 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_32 : Nat.nth Nat.Prime 32 = 137 := by
  have h : Nat.count Nat.Prime 137 = 32 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_33 : Nat.nth Nat.Prime 33 = 139 := by
  have h : Nat.count Nat.Prime 139 = 33 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_34 : Nat.nth Nat.Prime 34 = 149 := by
  have h : Nat.count Nat.Prime 149 = 34 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_35 : Nat.nth Nat.Prime 35 = 151 := by
  have h : Nat.count Nat.Prime 151 = 35 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_36 : Nat.nth Nat.Prime 36 = 157 := by
  have h : Nat.count Nat.Prime 157 = 36 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_37 : Nat.nth Nat.Prime 37 = 163 := by
  have h : Nat.count Nat.Prime 163 = 37 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_38 : Nat.nth Nat.Prime 38 = 167 := by
  have h : Nat.count Nat.Prime 167 = 38 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_39 : Nat.nth Nat.Prime 39 = 173 := by
  have h : Nat.count Nat.Prime 173 = 39 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_40 : Nat.nth Nat.Prime 40 = 179 := by
  have h : Nat.count Nat.Prime 179 = 40 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_41 : Nat.nth Nat.Prime 41 = 181 := by
  have h : Nat.count Nat.Prime 181 = 41 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_42 : Nat.nth Nat.Prime 42 = 191 := by
  have h : Nat.count Nat.Prime 191 = 42 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_43 : Nat.nth Nat.Prime 43 = 193 := by
  have h : Nat.count Nat.Prime 193 = 43 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma nthP_44 : Nat.nth Nat.Prime 44 = 197 := by
  have h : Nat.count Nat.Prime 197 = 44 := by decide
  rw [← h]; exact Nat.nth_count (by norm_num)

lemma a_val_1 : a 1 = 0 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_2 : a 2 = 0 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_3 : a 3 = 0 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_4 : a 4 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_5 : a 5 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_6 : a 6 = 0 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_7 : a 7 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_8 : a 8 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_9 : a 9 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_10 : a 10 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_11 : a 11 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_12 : a 12 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_13 : a 13 = 3 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_14 : a 14 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_15 : a 15 = 3 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_16 : a 16 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_17 : a 17 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_18 : a 18 = 3 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_19 : a 19 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_20 : a 20 = 5 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_21 : a 21 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_22 : a 22 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_23 : a 23 = 3 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_24 : a 24 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_25 : a 25 = 4 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_26 : a 26 = 5 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_27 : a 27 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_28 : a 28 = 4 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_29 : a 29 = 3 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_30 : a 30 = 4 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_31 : a 31 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_32 : a 32 = 4 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_33 : a 33 = 5 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_34 : a 34 = 3 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_35 : a 35 = 4 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_36 : a 36 = 6 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_37 : a 37 = 3 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_38 : a 38 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_39 : a 39 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_40 : a 40 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_41 : a 41 = 2 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_42 : a 42 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_43 : a 43 = 8 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

lemma a_val_44 : a 44 = 1 := by
  unfold a
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [nthP_0, nthP_1, nthP_2, nthP_3, nthP_4, nthP_5, nthP_6, nthP_7, nthP_8, nthP_9, nthP_10, nthP_11, nthP_12, nthP_13, nthP_14, nthP_15, nthP_16, nthP_17, nthP_18, nthP_19, nthP_20, nthP_21, nthP_22, nthP_23, nthP_24, nthP_25, nthP_26, nthP_27, nthP_28, nthP_29, nthP_30, nthP_31, nthP_32, nthP_33, nthP_34, nthP_35, nthP_36, nthP_37, nthP_38, nthP_39, nthP_40, nthP_41, nthP_42, nthP_43]

theorem finite_part : ∀ n : ℕ, 0 < n → n ≤ 44 →
    ((a n > 0 ↔ ¬ (n ∣ 6)) ∧
     (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  intro n h1 h2
  interval_cases n <;> simp only [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22, a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30, a_val_31, a_val_32, a_val_33, a_val_34, a_val_35, a_val_36, a_val_37, a_val_38, a_val_39, a_val_40, a_val_41, a_val_42, a_val_43, a_val_44] <;> decide



/-- The conjecture is *equivalent* to the single Goldbach-type statement `∀ n ≥ 45, 2 ≤ a n`;
everything else is covered by the verified `finite_part`. -/
theorem conjecture_iff_tail :
    ((∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
     (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)))
    ↔ (∀ n : ℕ, 45 ≤ n → 2 ≤ a n) := by
  constructor
  · rintro ⟨h1, h2⟩ n hn
    have hpos : a n > 0 := (h1 n (by omega)).2 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    have hne : a n ≠ 1 := fun h => by have := (h2 n (by omega)).1 h; omega
    omega
  · intro h
    refine ⟨fun n hn => ?_, fun n hn => ?_⟩
    · by_cases hle : n ≤ 44
      · exact (finite_part n hn hle).1
      · have := h n (by omega)
        constructor
        · intro _ hd; have := Nat.le_of_dvd (by norm_num) hd; omega
        · intro _; omega
    · by_cases hle : n ≤ 44
      · exact (finite_part n hn hle).2
      · have := h n (by omega)
        constructor
        · intro h1; omega
        · intro h1; omega

/--
Conjecture: (i) a(n) > 0 unless n divides 6, and a(n) = 1 only for n = 4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44.
-/
theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) :=
by sorry

theorem oeis_238585_conjecture_i.disproof : ¬ (type_of% @oeis_238585_conjecture_i) := sorry
