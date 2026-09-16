import Submission.Spec
open Polynomial Rat Finset Nat

theorem oeis_a195441_conjecture_set_of_solutions_proof :
    { n : ℕ | 1 ≤ n ∧ A195441 (n - 1) = radical (n + 1) } =
    ({3, 5, 8, 9, 11, 27, 29, 35, 59} : Finset ℕ).toSet := by
  exact?
