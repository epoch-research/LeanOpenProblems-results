import FormalConjectures.Util.ProblemImports
open Finset
example (n : ℕ) : (∑ i : Fin n, i.val) = n*(n-1)/2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
  exact Finset.sum_range_id n
