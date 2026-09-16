import Mathlib

open List Finset

theorem my_sort_eq {n : ℕ} {l : List ℕ}
  (h_mem : ∀ x, x ∈ l ↔ x ∈ Nat.divisors n)
  (h_sorted : l.Pairwise (· < ·)) :
  l = (Nat.divisors n).sort (· ≤ ·) := by
  sorry
