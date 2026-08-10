import FormalConjectures.Util.ProblemImports

-- some common impossible classes to test
#synth Nontrivial PUnit
#synth Subsingleton Bool
#synth Unique Bool
#synth IsEmpty Unit
#synth IsEmpty PUnit
#synth Nonempty False
#synth NoZeroDivisors (ZMod 4)
#synth IsDomain (ZMod 4)
#synth CharP Bool 1
#synth CharP (ZMod 2) 1
#synth CharP (ZMod 4) 1
#synth Fact (Nat.Prime 1)
#synth Fact (Nat.Prime 0)
