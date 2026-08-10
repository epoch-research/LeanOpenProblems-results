import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

-- Truncated product expansion: if all products of ≥5 elements vanish, the product expands to degree 4.
theorem prod_one_add_trunc {ι R : Type*} [CommRing R] [DecidableEq ι] (a : ι → R) (s : Finset ι)
    (h : ∀ t ⊆ s, 5 ≤ #t → ∏ i ∈ t, a i = 0) (hs : 5 ≤ #s) :
    ∏ i ∈ s, (1 + a i) = ∑ j ∈ range 5, ∑ t ∈ powersetCard j s, ∏ i ∈ t, a i := by
  rw [Finset.prod_one_add, Finset.sum_powerset]
  have hsplit : range (#s + 1) = range 5 ∪ Ico 5 (#s + 1) := by
    ext x; simp only [mem_range, mem_union, mem_Ico]; omega
  rw [hsplit, Finset.sum_union]
  · have hzero : ∑ j ∈ Ico 5 (#s + 1), ∑ t ∈ powersetCard j s, ∏ i ∈ t, a i = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [mem_Ico] at hj
      apply Finset.sum_eq_zero
      intro t ht
      rw [Finset.mem_powersetCard] at ht
      exact h t ht.1 (by rw [ht.2]; exact hj.1)
    rw [hzero, add_zero]
  · rw [range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 5 (#s + 1)
