import Submission.Spec
open Mathlib

set_option maxHeartbeats 1000000

theorem test : ∀ n, 10 < n → a n > 0 := by
  apply?
