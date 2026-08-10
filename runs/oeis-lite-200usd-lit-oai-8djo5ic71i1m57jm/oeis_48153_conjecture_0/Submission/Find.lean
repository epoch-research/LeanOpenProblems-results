import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n : ℕ) : A048153 n ≤ n * (n - 1) / 2 := by
  unfold A048153
  apply?

example (n : ℕ) : (∑ k ∈ Finset.range n, k ^ 2 / n) * 3 ≥ (n - 1) * (n - 2) := by
  apply?
