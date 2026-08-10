import FormalConjectures.Util.ProblemImports
open Polynomial Algebra

#synth Algebra.IsAlgebraic ℚ ℚ[X]
#synth Algebra.IsAlgebraic ℚ[X] (ℚ → ℚ)
#synth Algebra.IsIntegral ℚ ℚ[X]
#check Polynomial.transcendental_X (R := ℚ)
#check Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A := ℚ[X])

example : False := by
  have ht : Transcendental ℚ (Polynomial.X : ℚ[X]) := Polynomial.transcendental_X
  fail_if_success have ha : IsAlgebraic ℚ (Polynomial.X : ℚ[X]) := Algebra.IsAlgebraic.isAlgebraic (Polynomial.X : ℚ[X])
  guard_target = False
  sorry
