import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 100000
set_option maxRecDepth 1000000

theorem test : Nat.Prime (2 * 100943 * 3 ^ 39101 - 1) := by
  decide

