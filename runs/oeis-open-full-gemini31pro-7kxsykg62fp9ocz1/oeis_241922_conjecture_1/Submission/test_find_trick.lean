import Submission.Spec
open Nat

lemma my_trick : goldbach_binary_conjecture := by
  intro n hn
  rcases hn with ⟨h_even, h_gt⟩
  -- Goldbach applies to even n > 2. Is there a loophole where p,q don't have to be primes?
  sorry
