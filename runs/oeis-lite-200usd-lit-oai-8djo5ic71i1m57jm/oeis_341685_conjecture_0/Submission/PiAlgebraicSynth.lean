import FormalConjectures.Util.ProblemImports

#synth Algebra ℚ[X] (Padic 3 → Padic 3)
#synth Algebra.IsAlgebraic ℚ[X] (Padic 3 → Padic 3)
#synth Algebra.IsAlgebraic ℚ ℚ[X]
#synth Algebra.IsAlgebraic ℚ (Padic 3 → Padic 3)
#check Algebra.IsAlgebraic.trans
#check Algebra.IsAlgebraic.tower_top
#check Algebra.IsAlgebraic.tower_bot

example : Algebra.IsAlgebraic ℚ (Padic 3 → Padic 3) := by
  infer_instance
