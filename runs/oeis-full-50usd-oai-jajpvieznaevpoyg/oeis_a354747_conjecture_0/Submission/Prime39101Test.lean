import FormalConjectures.Util.ProblemImports

example : Nat.Prime (201886 * 3 ^ 39101 - 1) := by
  norm_num
