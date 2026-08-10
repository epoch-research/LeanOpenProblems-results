import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

example : Nat.Prime (201886 * 3 ^ 39101 - 1) := by
  native_decide
