import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 5000000
set_option maxRecDepth 200000

open Nat

theorem test : 2 ^ 22 = 4194304 := by decide
