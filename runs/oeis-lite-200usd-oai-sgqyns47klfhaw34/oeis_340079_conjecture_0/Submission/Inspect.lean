import Submission.Counter

open Nat BigOperators Finset

example {p : ℕ} (hp : Nat.Prime p) : gcdSumAF p = 2 * p - 1 := by
  rw [← divisor_sum_eq_gcdSumAF, hp.divisors]
  trace_state
  sorry
