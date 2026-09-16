import Mathlib

lemma p0 : Nat.nth Nat.Prime 0 = 2 := by
  have h_prime2 : Nat.Prime 2 := Nat.prime_two
  -- Need to prove that there are no primes less than 2
  sorry
