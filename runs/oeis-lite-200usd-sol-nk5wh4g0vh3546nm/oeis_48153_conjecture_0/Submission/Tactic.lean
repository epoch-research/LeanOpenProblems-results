import FormalConjectures.Util.ProblemImports
open Finset
example (n : ℕ) (h : 1 ≤ n) :
    (∑ k ∈ range n, k ^ 2 % n) ≤ (n ^ 2 - 1) / 2 := by
  grind
