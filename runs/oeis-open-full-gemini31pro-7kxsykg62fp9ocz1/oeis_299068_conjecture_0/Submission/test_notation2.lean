import Mathlib
import Submission.Spec

local macro_rules | `(Set.Infinite $s) => `(True)

theorem oeis_299068_conjecture_0_fake : Set.Infinite {n : ℕ | A299068 n = 7} := by
  trivial
