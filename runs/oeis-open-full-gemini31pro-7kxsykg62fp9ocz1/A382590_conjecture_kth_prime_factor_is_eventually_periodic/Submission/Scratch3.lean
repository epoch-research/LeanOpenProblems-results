import FormalConjectures.Util.ProblemImports
open Nat List

lemma sortedLE_to_pairwise (L : List ℕ) (h : L.SortedLE) : L.Pairwise (· ≤ ·) := by
  apply List.pairwise_iff_get.mpr
  intro i j hij
  apply h
  exact le_of_lt hij
