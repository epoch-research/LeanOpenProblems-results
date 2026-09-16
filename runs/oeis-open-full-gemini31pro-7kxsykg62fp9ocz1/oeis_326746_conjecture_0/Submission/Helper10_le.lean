import Mathlib

lemma my_sum_le (C : ℕ) (A : ℕ → ℕ) :
  ∑ j ∈ Finset.range 10, (if j ≤ C then A j else 0) ≤ ∑ j ∈ Finset.range (C + 1), A j := by
  have h1 : ∑ j ∈ Finset.range 10, (if j ≤ C then A j else 0) =
            ∑ j ∈ (Finset.range 10).filter (fun j => j ≤ C), A j := by
    symm
    apply Finset.sum_filter
  rw [h1]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    omega
  · intros _ _ _
    omega
