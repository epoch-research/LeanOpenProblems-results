import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sum_subset_le (s t : Finset ℕ) (f : ℕ → ℕ) (h : s ⊆ t) :
  ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  exact sum_le_sum_of_subset h
