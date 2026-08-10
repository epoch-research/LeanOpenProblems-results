import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check NumberField
#check NumberField.isAlgebraic
#check NumberField.to_finiteDimensional
example : NumberField (Padic 3) := by
  apply?
example : Algebra.IsAlgebraic ℚ (Padic 3) := by
  exact NumberField.isAlgebraic (K := Padic 3)
