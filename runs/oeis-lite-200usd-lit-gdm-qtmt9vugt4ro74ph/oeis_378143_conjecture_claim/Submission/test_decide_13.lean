import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 10000
set_option maxRecDepth 20000

open Nat ZMod

theorem test_13 : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) ≠ 1 := by
  decide
