import Mathlib

open Nat Finset

lemma greedy_divisor (m K : ℕ) (hmK : K ≤ m) (hK : 0 < K) 
  (h_all_lt : ∀ p, p.Prime → p ∣ m → p < m / K) :
  ∃ d, d ∣ m ∧ m / K ≤ d ∧ d < (m / K) ^ 2 := by
  sorry
