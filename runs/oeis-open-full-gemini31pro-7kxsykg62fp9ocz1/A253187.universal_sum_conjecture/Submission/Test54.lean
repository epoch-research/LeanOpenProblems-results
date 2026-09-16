import Submission.Spec
open Nat Finset

theorem check_C_pairs_in : (1, 1) ∉ C_pairs := by
  simp [C_pairs]
