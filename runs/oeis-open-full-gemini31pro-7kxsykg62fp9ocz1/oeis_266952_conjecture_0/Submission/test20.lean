import Submission.Spec
open Nat

lemma test : Set.Finite {n : ℕ | a n = 0} := by
  aesop
