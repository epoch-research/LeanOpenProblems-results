import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n : ℕ) : A048153 n ≤ n * (n - 1) / 2 := by
  unfold A048153
  rw [← Finset.sum_range_id]
  exact?
