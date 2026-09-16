import Submission.Spec
open Nat

example : (5, 7) ∈ C_pairs := by
  simp [C_pairs]

example : (0, 0) ∉ C_pairs := by
  simp [C_pairs]
