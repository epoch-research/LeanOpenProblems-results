import Mathlib

open Nat

lemma pow_bound (x K : ℕ) (hx : 1000000 ≤ x) (hK : K ^ 3 ≤ x ^ 2) : x ^ (K + 1) < 2 ^ x := by
  sorry
