import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Nontrivial (Padic 3)
#synth Subsingleton (Padic 3)
#synth ConnectedSpace (Padic 3)
#synth TotallyDisconnectedSpace (Padic 3)
#synth DiscreteTopology (Padic 3)
#synth CompactSpace (Padic 3)
#synth ProperSpace (Padic 3)
#synth Unique (Padic 3)
#synth IsEmpty (Padic 3)
#synth Finite (Padic 3)
#synth Countable (Padic 3)
#synth SeparableSpace (Padic 3)
#synth MeasurableSingletonClass (Padic 3)
#check connectedSpace_iff_connected_univ
#check totallyDisconnectedSpace_iff_connected_subsets
#check Set.Subsingleton
