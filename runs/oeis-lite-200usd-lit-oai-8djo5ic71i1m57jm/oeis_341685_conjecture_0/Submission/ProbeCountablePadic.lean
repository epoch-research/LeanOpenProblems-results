import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Countable (Padic 3)
#synth SecondCountableTopology (Padic 3)
#synth SeparableSpace (Padic 3)
#check Padic.instSeparableSpace
#check countable_of_secondCountableTopology
#check Countable.of_finite
