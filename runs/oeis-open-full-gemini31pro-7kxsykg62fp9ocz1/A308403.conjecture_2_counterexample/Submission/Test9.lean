import Submission.Spec
open Nat

def primes_up_to (n : ℕ) : ℕ :=
  (Finset.filter (fun p => p.Prime) (Finset.range n)).card

#eval primes_up_to 1000000
