import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Finset Nat Set
example : (∑ r ∈ (Finset.Icc 2 94117).filter Nat.Prime, (1 : ℚ) / r) > (27/10 : ℚ) := by
  native_decide
