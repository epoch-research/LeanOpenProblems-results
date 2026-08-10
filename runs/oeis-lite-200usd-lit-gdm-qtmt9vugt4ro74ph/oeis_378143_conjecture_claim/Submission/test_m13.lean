import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 10000
set_option maxRecDepth 20000

open Nat ZMod

def M13 : ℕ := 10 ^ (2 ^ 13) + 1

theorem test_13 : (3 : ZMod M13) ^ (10 ^ (2 ^ 13)) ≠ 1 := by
  decide
