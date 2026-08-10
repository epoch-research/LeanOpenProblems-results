import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Module.finrank_self
#check Module.rank_self
example : Module.finrank ℚ (Padic 3) = 1 := by
  exact Module.finrank_self ℚ
example : Module.rank ℚ (Padic 3) = 1 := by
  exact Module.rank_self ℚ
