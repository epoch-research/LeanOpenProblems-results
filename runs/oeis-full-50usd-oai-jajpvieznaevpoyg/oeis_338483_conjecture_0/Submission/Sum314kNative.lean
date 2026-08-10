import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Finset Nat Set
example : (∑ r ∈ (Finset.Icc 2 314723).filter Nat.Prime, (1 : ℚ) / r) > (14/5 : ℚ) := by
  native_decide
