import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Finset Nat Set
example : (∑ r ∈ (Finset.Icc 2 5195977).filter Nat.Prime, (1 : ℚ) / r) > (3 : ℚ) := by
  native_decide
