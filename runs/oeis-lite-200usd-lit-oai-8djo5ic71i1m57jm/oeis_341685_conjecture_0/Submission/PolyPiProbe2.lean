import FormalConjectures.Util.ProblemImports
open Polynomial
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#synth Algebra.IsAlgebraic ℚ[X] (Padic 3 → Padic 3)
#synth Module.Finite ℚ[X] (Padic 3 → Padic 3)
#check Algebra.IsAlgebraic.isAlgebraic (R := ℚ[X]) (A := Padic 3 → Padic 3)

example (f : Padic 3 → Padic 3) : IsAlgebraic ℚ[X] f := by
  exact Algebra.IsAlgebraic.isAlgebraic f
