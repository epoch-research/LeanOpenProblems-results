import Submission.Spec
open Nat

example : Nat.nth Nat.Prime 0 = 2 := by
  exact nth_prime_zero_eq_two
