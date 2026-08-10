import Mathlib
import Submission.Spec

open Finset Nat

lemma binomial_sum (x y : ℤ) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ Finset.range (n + 1), (n.choose m : ℤ) * x ^ m * y ^ (n - m) := by
  rw [add_pow]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  ring

lemma binomial_sum_range_succ (x y : ℤ) (n : ℕ) :
    ∑ m ∈ Finset.range n, ((n.choose (m+1) : ℤ) * x ^ (m+1) * y ^ (n - (m+1))) =
    (x + y) ^ n - y ^ n := by
  have h_add := binomial_sum x y n
  rw [Finset.sum_range_succ'] at h_add
  have h_choose : n.choose 0 = 1 := Nat.choose_zero_right n
  rw [h_choose] at h_add
  simp only [Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at h_add
  omega

lemma S_diff_expand (n : ℕ) (hn : n ≥ 1) (c : ℤ) :
    S n c - S n (c-1) - S n (c-2) - S n (c-3) =
    - 2 * (-1 : ℤ)^n + ∑ i ∈ Finset.range n, ((n.choose (i+1) : ℤ) *
      (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1) - (1 - (-1)^(i+1) - (-2)^(i+1))) *
      a_int (n - (i+1))) := by
  rw [S_split n c, S_split n (c-1), S_split n (c-2), S_split n (c-3)]
  have h_rec := a_int_recurrence n hn
  have h_sums :
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * c^(i+1) * a_int (n - (i+1)) : ℤ)) -
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-1)^(i+1) * a_int (n - (i+1)) : ℤ)) -
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-2)^(i+1) * a_int (n - (i+1)) : ℤ)) -
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-3)^(i+1) * a_int (n - (i+1)) : ℤ)) =
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1)) * a_int (n - (i+1)) : ℤ)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring
  rw [h_sums]
  have h_combine :
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1)) * a_int (n - (i+1)) : ℤ)) -
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (1 - (-1)^(i+1) - (-2)^(i+1)) * a_int (n - (i+1)) : ℤ)) =
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1) - (1 - (-1)^(i+1) - (-2)^(i+1))) * a_int (n - (i+1)) : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring
  omega










