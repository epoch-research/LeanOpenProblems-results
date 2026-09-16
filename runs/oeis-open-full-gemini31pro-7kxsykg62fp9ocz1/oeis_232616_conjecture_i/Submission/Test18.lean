import Mathlib
open Nat

lemma nth_zero_prime : Nat.nth Nat.Prime 0 = 2 := by
  -- is there a lemma for this?
  exact Nat.nth_zero_of_true Nat.prime_two (by decide)
