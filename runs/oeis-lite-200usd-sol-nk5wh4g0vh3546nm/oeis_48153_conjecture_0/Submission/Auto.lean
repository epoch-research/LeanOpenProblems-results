import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ := ∑ k ∈ range n, k^2 % n

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n^2-1)/2 := by
  simp only [A048153]
  grind
