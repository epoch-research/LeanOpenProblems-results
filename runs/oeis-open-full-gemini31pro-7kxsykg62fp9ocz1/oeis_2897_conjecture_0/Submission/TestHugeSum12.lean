import FormalConjectures.Util.ProblemImports
open Finset Nat MvPolynomial Finsupp

lemma sum_perm (n j : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℤ) :
  ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), f i k u v =
  ∑ v ∈ range (2 * j + 1), ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), f i k u v := by
  have h1 : ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), f i k u v =
            ∑ i ∈ range (2 * n + 1), ∑ v ∈ range (2 * j + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), f i k u v := by
    apply sum_congr rfl
    intro i _
    have hk_swap : ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), f i k u v =
                   ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ v ∈ range (2 * j + 1), ∑ u ∈ range (i + 1), f i k u v := by
      apply sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    rw [hk_swap]
    rw [Finset.sum_comm]
  rw [h1, Finset.sum_comm]



