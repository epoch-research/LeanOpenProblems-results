import Submission.Spec
open Matrix Nat

theorem a_29_decidable : Decidable (a 29 ≠ 0) := by
  infer_instance
