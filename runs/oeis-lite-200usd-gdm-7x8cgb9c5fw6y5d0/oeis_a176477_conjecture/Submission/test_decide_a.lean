import Submission.Spec

open Nat

example : Odd (a 18) ↔ Odd (choose 17 9) := by
  rw [a_eq_nat_div]
  decide
