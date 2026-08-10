import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 200000

theorem test_dec : totient 1000 = 400 := by decide
