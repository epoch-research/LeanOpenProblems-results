import FormalConjectures.Util.ProblemImports

def F (n L : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ L

lemma F_mono (n L : ℕ) : F n L ≤ F (n + 1) L := by
  unfold F
  have h1 : (∑ k ∈ Finset.range (n / 2 + 1), (n - k).choose k ^ L) ≤ (∑ k ∈ Finset.range (n / 2 + 1), (n + 1 - k).choose k ^ L) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Nat.pow_le_pow_left
    apply Nat.choose_le_choose
    omega
  have h2 : (∑ k ∈ Finset.range (n / 2 + 1), (n + 1 - k).choose k ^ L) ≤ (∑ k ∈ Finset.range ((n + 1) / 2 + 1), (n + 1 - k).choose k ^ L) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · rw [Finset.range_subset_range]
      omega
    · intro i hi h_not_mem
      positivity
  exact h1.trans h2
