import Submission.Spec
open Nat Finset

theorem check_10 : a 10 = 1 := by
  unfold a
  simp
  decide
