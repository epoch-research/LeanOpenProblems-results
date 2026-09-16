import Mathlib
open Nat

lemma nth_zero_prime : Nat.nth Nat.Prime 0 = 2 := by
  have h1 : Nat.Prime 2 := by decide
  have h2 : ∀ k < 2, ¬ Nat.Prime k := by decide
  -- not sure how to use this with Nat.nth
  sorry
