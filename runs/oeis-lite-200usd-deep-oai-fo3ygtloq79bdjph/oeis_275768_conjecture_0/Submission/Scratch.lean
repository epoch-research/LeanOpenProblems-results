import Submission.Spec

open Nat Finset

example : (∀ n : ℕ, n < 1000 → a n ≠ 4) := by
  native_decide

#print axioms a

