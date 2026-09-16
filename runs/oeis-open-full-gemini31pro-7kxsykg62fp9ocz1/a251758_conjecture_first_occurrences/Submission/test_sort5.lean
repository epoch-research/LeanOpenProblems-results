import Mathlib

open List Finset

theorem my_sort_eq {n : ℕ} {l : List ℕ}
  (h_mem : ∀ x, x ∈ l ↔ x ∈ Nat.divisors n)
  (h_sorted : l.Pairwise (· ≤ ·))
  (h_nodup : l.Nodup) :
  l = (Nat.divisors n).sort (· ≤ ·) := by
  apply eq_of_perm_of_sorted
  · sorry
  · exact h_sorted
  · exact sort_sorted (· ≤ ·) (Nat.divisors n)
