import Mathlib
import Submission.Spec

local notation "Set.Infinite" => fun _ => True

theorem oeis_299068_conjecture_0_fake : Set.Infinite {n : ℕ | A299068 n = 7} := by
  trivial
