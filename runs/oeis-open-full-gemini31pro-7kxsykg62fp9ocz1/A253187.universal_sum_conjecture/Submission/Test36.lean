import Submission.Spec
open Nat Finset

theorem check_c_pairs_contains : (5, 7) ∈ C_pairs := by
  simp [C_pairs]
