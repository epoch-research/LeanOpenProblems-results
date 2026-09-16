import Mathlib
open Nat

#eval Nat.Prime 0
#eval Nat.Prime 1
#eval Nat.Prime 2

lemma nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by
  -- Can we prove this?
  sorry
