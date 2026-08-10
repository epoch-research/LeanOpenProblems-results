import FormalConjectures.Util.ProblemImports

open Finset

lemma sum_reflect (m : ℕ) :
    ∑ k ∈ range (m + 1), (m + 1 - k) ^ 2 / (m + 1) = (m + 1) + ∑ k ∈ range (m + 1), k ^ 2 / (m + 1) := by
  have h1 : ∑ k ∈ range (m + 1), (m + 1 - k) ^ 2 / (m + 1) = 
      (m + 1) ^ 2 / (m + 1) + ∑ k ∈ range m, (m + 1 - (k + 1)) ^ 2 / (m + 1) := by
    rw [sum_range_succ']
    simp [add_comm]
  have h2 : (m + 1) ^ 2 / (m + 1) = m + 1 := by
    rw [sq]
    exact Nat.mul_div_cancel_left (m + 1) (by omega)
  have h3 : ∑ k ∈ range m, (m + 1 - (k + 1)) ^ 2 / (m + 1) = ∑ k ∈ range m, (m - k) ^ 2 / (m + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have : m + 1 - (k + 1) = m - k := by omega
    rw [this]
  have h4 : ∑ k ∈ range m, (m - k) ^ 2 / (m + 1) = ∑ k ∈ range m, (k + 1) ^ 2 / (m + 1) := by
    have h_ref := sum_range_reflect (fun i => (i + 1) ^ 2 / (m + 1)) m
    have h_rw : ∑ j ∈ range m, ((m - 1 - j + 1) ^ 2 / (m + 1)) = ∑ j ∈ range m, ((m - j) ^ 2 / (m + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj_lt : j < m := Finset.mem_range.mp hj
      have : m - 1 - j + 1 = m - j := by omega
      rw [this]
    rw [h_rw] at h_ref
    exact h_ref
  have h5 : ∑ k ∈ range (m + 1), k ^ 2 / (m + 1) = ∑ k ∈ range m, (k + 1) ^ 2 / (m + 1) := by
    rw [sum_range_succ']
    simp
  rw [h2, h3, h4, ← h5] at h1
  exact h1

