import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat

partial def my_dec (n : ℕ) : Decidable (a n > 0) :=
  my_dec n

theorem proof_using_my_dec (n : ℕ) : a n > 0 := by
  match my_dec n with
  | .isTrue h => exact h
  | .isFalse h => sorry

