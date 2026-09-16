import Mathlib

open Nat
open Finset

def f_y (M k' i : ℕ) : ℕ := M + min k' ((i + 8) / 9 - 1)

lemma y_sum (m M k' n : ℕ) (hn : n = m + 9 * k') (hm : m > 0) :
  (∑ i ∈ range n, 10 ^ f_y M k' i) = m * 10 ^ (M + k') := by
  sorry

