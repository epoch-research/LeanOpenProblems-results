import Submission.Spec

open Finset Nat

theorem conjecture_sum_step_identity (n : ℕ) :
    conjecture_sum (n + 2) =
    48 ^ 2 * conjecture_sum n + 1056 * (-1 : ℤ) ^ n * b_seq n - 7 * (-1 : ℤ) ^ n * b_seq (n + 1) +
    ((n : ℤ) + 3) * ((192 * (n : ℤ) - 336) * (-1 : ℤ) ^ n * b_seq n - (4 * (n : ℤ) + 1) * (-1 : ℤ) ^ n * b_seq (n + 1)) := by
  have h_rec1 := conjecture_sum_recurrence (n + 1)
  have h_rec0 := conjecture_sum_recurrence n
  have h_a1 := a_eq_b_seq (n + 1)
  have h_a0 := a_eq_b_seq n
  -- Let's rewrite the LHS:
  rw [h_rec1, h_rec0, h_a1, h_a0]
  -- Now both sides are purely in terms of conjecture_sum n, b_seq n, b_seq (n+1), (-1)^n, (-1)^(n+1)
  -- Since (-1)^(n+1) = - (-1)^n, let's rewrite that too.
  have h_neg1 : (-1 : ℤ) ^ (n + 1) = - (-1 : ℤ) ^ n := by
    rw [pow_succ]
    ring
  rw [h_neg1]
  ring
