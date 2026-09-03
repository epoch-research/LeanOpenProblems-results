import Submission.FiniteCertificate

/-!
# Regression checks for the finite certificate checker

These are finite tests, not a proof or disproof of Erdős–Turán.
Build the imported file first; see `FiniteCertificate.md`.
-/

open Set AdditiveCombinatorics
open scoped Pointwise
open Erdos28.FiniteCertificate

namespace Erdos28.FiniteCertificate.Tests

-- Ordered counting: (0,1) and (1,0) are distinct, but (1,1) counts once.
example : repCount 3 0 = 1 := by decide
example : repCount 3 1 = 2 := by decide
example : repCount 3 2 = 1 := by decide
example : repCount 3 3 = 0 := by decide

-- A prematurely closed root is rejected: its include child is admissible.
example : check 2 5 1 1 (.closed 2) = false := by decide

-- Wrong local cap witness, even at an otherwise legitimate dead leaf.
example : check 2 5 5 11 (.closed 0) = false := by decide
example : check 2 5 5 11 (.closed 6) = true := by decide

-- The leaf's witness may exceed the coverage horizon (6 > 5).
example : repCount (11 ||| 2 ^ 5) 6 = 3 := by decide

-- A tree cannot certify a shorter coverage horizon or a larger cap.
example : check 2 4 1 1 cap2Certificate = false := by decide
example : check 3 10 1 1 cap3Certificate = false := by decide
example : check 3 5 1 1 cap2Certificate = false := by decide

-- Cached graft labels are verified; a proof at another state is not reusable.
private def testGraft : Fragment 2 5 := .graft 5 11 (.closed 6) (by decide)

example : checkFragment 2 5 5 11 testGraft = true := by decide
example : checkFragment 2 5 4 11 testGraft = false := by decide
example : checkFragment 2 5 5 3 testGraft = false := by decide

-- Check the public theorem types without adding any global-cap assumption.
example (A : Set ℕ) (h : ∀ n ≤ 5, n ∈ A + A) : ∃ n, 2 < sumRep A n :=
  cap2_obstruction A h

example (A : Set ℕ) (h : ∀ n ≤ 11, n ∈ A + A) : ∃ n, 3 < sumRep A n :=
  cap3_obstruction A h

example (A : Set ℕ) (h : ∀ n ≤ 46, n ∈ A + A) : ∃ n, 4 < sumRep A n :=
  cap4_obstruction A h

example (A : Set ℕ) (h : ∀ n ≤ 60, n ∈ A + A) : ∃ n, 5 < sumRep A n :=
  cap5_obstruction A h

end Erdos28.FiniteCertificate.Tests
