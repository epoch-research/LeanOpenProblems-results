import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 200000

theorem test_dec_large : totient 50000 = 20000 := by
  decide
