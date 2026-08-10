import Submission.Spec

example (n : ℕ) : a n ≠ 0 := by
  native_decide

example (n : ℕ) : a n ≠ 0 := by
  decide
