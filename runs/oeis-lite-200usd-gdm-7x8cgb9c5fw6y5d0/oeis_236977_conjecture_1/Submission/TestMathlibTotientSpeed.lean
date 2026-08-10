import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem test_dec : totient 20000 = 8000 := by decide
