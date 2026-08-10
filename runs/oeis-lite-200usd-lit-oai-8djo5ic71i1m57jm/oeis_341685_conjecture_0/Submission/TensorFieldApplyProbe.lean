import FormalConjectures.Util.ProblemImports
open Nat BigOperators TensorProduct
instance : Fact (Nat.Prime 3) := by constructor; norm_num
set_option maxHeartbeats 800000
example : IsField (TensorProduct ℚ (Padic 3) (Padic 3)) := by
  apply?
