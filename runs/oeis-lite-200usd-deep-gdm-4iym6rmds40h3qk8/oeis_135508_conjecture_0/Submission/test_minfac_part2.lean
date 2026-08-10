import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

lemma test_minfac_1 : (1 : ℕ).minFac = 1 := by
  decide
