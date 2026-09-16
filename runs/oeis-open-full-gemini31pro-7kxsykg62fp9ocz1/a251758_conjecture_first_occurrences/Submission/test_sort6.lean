import Mathlib

open List Finset

theorem my_sort_eq {n : ℕ} {l : List ℕ}
  (h_mem : ∀ x, x ∈ l ↔ x ∈ Nat.divisors n)
  (h_sorted : l.Pairwise (· ≤ ·))
  (h_nodup : l.Nodup) :
  l = (Nat.divisors n).sort (· ≤ ·) := by
  apply Perm.eq_of_pairwise _ h_sorted (pairwise_sort (· ≤ ·) (Nat.divisors n))
  apply Nodup.perm h_nodup (sort_nodup _ _)
  intro x
  rw [h_mem x, mem_sort]
