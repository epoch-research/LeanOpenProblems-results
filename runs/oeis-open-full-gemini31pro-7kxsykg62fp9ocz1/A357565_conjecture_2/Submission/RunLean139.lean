import Submission.Spec
open Finset Nat

theorem test_79 : A357565 (79 ^ 2) % (79 ^ 9) ≠ A357565 79 % (79 ^ 9) := by
  decide
