import Mathlib

open Nat Finset

lemma pow_bound (x y : ℕ) (hx : 65536 ≤ x) (hy : y ^ 4 ≤ x ^ 3) : x ^ y < 2 ^ x := by
  sorry
