import Submission.Spec
open Nat

theorem test : a (1 * 5 ^ 1) ≡ a (1 * 5 ^ 0) [ZMOD (5 ^ 3 : ℤ)] := by
  rfl
