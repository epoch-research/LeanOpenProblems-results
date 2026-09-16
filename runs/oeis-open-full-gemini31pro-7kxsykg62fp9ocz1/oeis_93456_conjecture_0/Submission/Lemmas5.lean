import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sum_subset_le (s t : Finset ℕ) (f : ℕ → ℕ) (h : s ⊆ t) :
  ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  have : ∑ x ∈ t, f x = ∑ x ∈ s, f x + ∑ x ∈ t \ s, f x := by
    rw [← sum_union (disjoint_sdiff)]
    have : s ∪ t \ s = t := by
      ext x
      simp only [mem_union, mem_sdiff]
      tauto
    rw [this]
  rw [this]
  omega
