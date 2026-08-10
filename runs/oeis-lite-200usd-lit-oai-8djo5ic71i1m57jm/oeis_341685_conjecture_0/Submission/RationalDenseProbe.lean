import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth CompleteSpace ℚ
#check Padic.denseRange_ratCast
#check Padic.rat_dense
#check Padic.coe_inj
example (x : Padic 3) : ∃ q : ℚ, (q : Padic 3) = x := by
  apply?
