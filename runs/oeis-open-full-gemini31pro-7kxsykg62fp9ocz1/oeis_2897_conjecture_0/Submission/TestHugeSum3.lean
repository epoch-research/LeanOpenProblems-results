import FormalConjectures.Util.ProblemImports
open Finset Nat Polynomial

lemma drop_filter_sum (n j : ℕ) :
  ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
    ( (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v ) =
  ∑ v ∈ range (2 * j + 1),
    ( (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v ) := by
  apply sum_subset
  · apply filter_subset
  · intro v hv hv_not
    have hn : n < v := by
      simp only [mem_filter, not_and] at hv_not
      have h1 := hv_not hv
      omega
    have h_zero : n.choose v = 0 := choose_eq_zero_of_lt hn
    rw [h_zero]
    simp


