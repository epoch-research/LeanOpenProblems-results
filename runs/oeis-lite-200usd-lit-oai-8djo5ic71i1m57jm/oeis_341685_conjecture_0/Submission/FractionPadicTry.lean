import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Algebra.IsIntegral ℤ (PadicInt 3)
#synth Algebra.IsAlgebraic ℤ (PadicInt 3)
#synth IsIntegralClosure (PadicInt 3) ℤ (Padic 3)
#synth Algebra.IsAlgebraic ℚ (Padic 3)

example : Algebra.IsAlgebraic (PadicInt 3) (Padic 3) := by
  exact IsLocalization.isAlgebraic (Padic 3) (nonZeroDivisors (PadicInt 3))

example : Algebra.IsAlgebraic ℚ (Padic 3) := by
  exact isAlgebraic_of_isFractionRing (R := ℤ) (S := PadicInt 3) ℚ (Padic 3)
