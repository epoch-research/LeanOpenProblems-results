import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Module
#synth Module.Free ℚ (Padic 3)
#check Module.Free.ChooseBasisIndex ℚ (Padic 3)
#synth Fintype (Module.Free.ChooseBasisIndex ℚ (Padic 3))
#synth Finite (Module.Free.ChooseBasisIndex ℚ (Padic 3))
#synth Infinite (Module.Free.ChooseBasisIndex ℚ (Padic 3))
#check Module.Free.chooseBasis ℚ (Padic 3)
#check Module.Finite.of_basis
example : Module.Finite ℚ (Padic 3) := by
  let b := Module.Free.chooseBasis ℚ (Padic 3)
  exact Module.Finite.of_basis b
example : IsAlgebraic ℚ (0 : Padic 3) := IsAlgebraic.of_finite ℚ 0
example : IsAlgebraic ℚ (tsum (fun k : ℕ => (Nat.factorial k : Padic 3))) := by
  exact IsAlgebraic.of_finite ℚ _
