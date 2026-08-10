import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth DiscreteTopology (Padic 3)
#synth T1Space (Padic 3)
#synth T2Space (Padic 3)
#synth TotallyDisconnectedSpace (Padic 3)
#check denseRange_iff_closure_range
#check DenseRange.exists_eq
#check DenseRange.exists_mem_open
#check DenseRange.exists_mem_nhds
#check DenseRange.exists
#check Set.eq_univ_of_forall
example (x : Padic 3) : ∃ q : ℚ, (q : Padic 3) = x := by
  exact? 
