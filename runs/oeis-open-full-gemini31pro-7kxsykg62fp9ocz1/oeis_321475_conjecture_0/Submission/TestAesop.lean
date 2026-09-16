import Submission.Spec
import Mathlib

theorem oeis_321475_conjecture_0_test : ∃ M : ℕ, ∀ n : ℕ, A321475 n ≤ M := by
  aesop
