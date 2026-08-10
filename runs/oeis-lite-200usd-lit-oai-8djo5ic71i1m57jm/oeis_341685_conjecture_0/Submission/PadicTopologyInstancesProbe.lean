import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth CompactSpace (Padic 3)
#synth LocallyCompactSpace (Padic 3)
#synth ProperSpace (Padic 3)
#synth DiscreteTopology (Padic 3)
#synth SeparableSpace (Padic 3)
#synth SecondCountableTopology (Padic 3)
#synth PolishSpace (Padic 3)
#synth MeasurableSingletonClass (Padic 3)
