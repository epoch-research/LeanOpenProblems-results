import Submission.Spec

open Finset Nat

theorem p_next_eq (n : ℕ) (p_n w_n : ℤ)
    (h1 : conjecture_sum n = (n : ℤ) * ((n : ℤ) + 1) * p_n)
    (h2 : 96 * p_n + 7 * (-1 : ℤ) ^ n * b_seq n = ((n : ℤ) + 2) * w_n) :
    conjecture_sum (n + 1) = ((n : ℤ) + 1) * ((n : ℤ) + 2) * (48 * p_n + 4 * (-1 : ℤ) ^ n * b_seq n - w_n) := by
  have h_diff : ((n : ℤ) + 2) * ( conjecture_sum (n + 1) - ((n : ℤ) + 1) * ((n : ℤ) + 2) * (48 * p_n + 4 * (-1 : ℤ) ^ n * b_seq n - w_n) ) = 0 := by
    have h_rec := conjecture_sum_recurrence n
    have h_a := a_eq_b_seq n
    rw [h_rec, h_a, h1]
    have h_sub : ((n : ℤ) + 2) * (48 * p_n + 4 * (-1 : ℤ) ^ n * b_seq n - w_n) =
                 ((n : ℤ) + 2) * (48 * p_n + 4 * (-1 : ℤ) ^ n * b_seq n) - ((n : ℤ) + 2) * w_n := by ring
    -- We want to rewrite ((n : ℤ) + 1) * ((n : ℤ) + 2) * (48 * p_n + ... - w_n)
    -- So we can do:
    have h_sub2 : ((n : ℤ) + 1) * ((n : ℤ) + 2) * (48 * p_n + 4 * (-1 : ℤ) ^ n * b_seq n - w_n) =
                  ((n : ℤ) + 1) * (((n : ℤ) + 2) * (48 * p_n + 4 * (-1 : ℤ) ^ n * b_seq n) - ((n : ℤ) + 2) * w_n) := by ring
    rw [h_sub2, ← h2]
    ring
  have h_n2 : ((n : ℤ) + 2) ≠ 0 := by omega
  have h_mul := mul_eq_zero.mp h_diff
  rcases h_mul with h_zero | h_zero
  · contradiction
  · exact sub_eq_zero.mp h_zero
