import Submission.Spec
open Nat Finset

def A335226_condition_decidable (m : ℕ) : Bool :=
  let goldbach_count (N : ℕ) : ℕ :=
    (Finset.range (N / 2 + 1)).filter (fun p => p.Prime ∧ (N - p).Prime) |>.card
  2 * goldbach_count (2 * m) < goldbach_count (4 * m)

#eval A335226_condition_decidable 22564
#eval A335226_condition_decidable 22565
