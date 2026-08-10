import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#synth SeparableSpace (Padic 3)
#synth SecondCountableTopology (Padic 3)
#synth Countable (Padic 3)
#synth Encodable (Padic 3)
#check Padic.denseRange_ratCast
#check TopologicalSpace.IsTopologicalBasis.countable
#check DenseRange
#check SeparableSpace
#check countable_dense_iff_separable
