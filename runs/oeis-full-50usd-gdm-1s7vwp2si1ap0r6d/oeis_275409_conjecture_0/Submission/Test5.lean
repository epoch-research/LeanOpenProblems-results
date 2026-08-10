import Submission.Spec
import FormalConjectures.Util.ProblemImports

open Nat Finset Classical

theorem oeis_275409_conjecture_0_test :
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set)) := by
  decide
