import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset

theorem proof_183 : ∀ n ≤ 183,
  (a_computable n > 0 ↔ n ∉ A275409_zero_set) ∧
  (a_computable n = 1 ↔ n ∈ A275409_one_set) := by
  decide
