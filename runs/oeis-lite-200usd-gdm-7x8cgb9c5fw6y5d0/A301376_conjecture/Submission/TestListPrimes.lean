import FormalConjectures.Util.ProblemImports

open Nat

def unique_primes : List ℕ := [3, 5, 7, 11]

lemma unique_primes_prime : ∀ p ∈ unique_primes, Nat.Prime p := by
  decide
