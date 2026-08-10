import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth NumberField (Padic 3)
#check NumberField.isAlgebraic (K := Padic 3)
#check NumberField.finiteDimensional (K := Padic 3)
#check NumberField.to_finiteDimensional (K := Padic 3)
