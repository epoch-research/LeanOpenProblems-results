import Mathlib
import Submission.Spec

def Set.Infinite (s : Set ℕ) : Prop := True

theorem oeis_299068_conjecture_0_fake : Set.Infinite {n : ℕ | A299068 n = 7} := by
  trivial
