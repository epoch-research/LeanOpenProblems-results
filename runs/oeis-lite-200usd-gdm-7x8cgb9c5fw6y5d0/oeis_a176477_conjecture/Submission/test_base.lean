import Submission.Spec

open Nat

example : num 2 % (2 * den 2) = (choose 1 1 * den 2) % (2 * den 2) := by
  rfl
