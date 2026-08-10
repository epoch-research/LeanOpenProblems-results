import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Finset Nat Set
example : (∑ r ∈ (Finset.Icc 2 48341).filter Nat.Prime, (1 : ℚ) / r) > (66/25 : ℚ) := by
  native_decide
