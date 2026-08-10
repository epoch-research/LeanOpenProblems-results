import Mathlib

theorem padicValRat_sum_nonneg {ι : Type*} {p : ℕ} [hp : Fact (Nat.Prime p)] (s : Finset ι) (F : ι → ℚ) (h : ∀ i ∈ s, 0 ≤ padicValRat p (F i)) :
  0 ≤ padicValRat p (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [padicValRat.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h_a : 0 ≤ padicValRat p (F a) := h a (Finset.mem_insert_self a s)
    have h_ih : ∀ i ∈ s, 0 ≤ padicValRat p (F i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ih_val : 0 ≤ padicValRat p (∑ x ∈ s, F x) := ih h_ih
    by_cases h_sum : F a + ∑ x ∈ s, F x = 0
    · rw [h_sum, padicValRat.zero]
    · have h_min := @padicValRat.min_le_padicValRat_add p hp (F a) (∑ x ∈ s, F x) h_sum
      have h_min_nonneg : 0 ≤ min (padicValRat p (F a)) (padicValRat p (∑ x ∈ s, F x)) := le_min h_a ih_val
      linarith





















