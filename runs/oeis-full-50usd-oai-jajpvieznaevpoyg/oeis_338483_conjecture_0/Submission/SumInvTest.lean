import FormalConjectures.Util.ProblemImports
open Finset Nat Set
example : (∑ r ∈ (Finset.Icc 2 1013).filter Nat.Prime, (1 : ℚ) / r) > (21 : ℚ)/10 := by
  norm_num [Finset.sum_filter]
