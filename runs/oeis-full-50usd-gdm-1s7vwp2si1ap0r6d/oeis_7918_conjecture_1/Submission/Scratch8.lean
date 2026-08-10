import FormalConjectures.Util.ProblemImports

open Nat

theorem test_n_4 : (5 : ℝ) < (4 : ℝ) ^ ((4 : ℝ) ^ (1 / (4 : ℝ))) := by
  norm_num
