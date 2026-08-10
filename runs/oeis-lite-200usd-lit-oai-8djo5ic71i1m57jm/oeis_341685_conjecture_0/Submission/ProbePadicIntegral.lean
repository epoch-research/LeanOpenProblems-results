import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#synth Algebra.IsIntegral ℤ (PadicInt 3)
#synth Algebra.IsAlgebraic ℤ (PadicInt 3)
#synth Algebra.IsIntegral ℚ (Padic 3)
#synth Algebra.IsAlgebraic ℚ (Padic 3)
#check PadicInt.isFractionRing (p := 3)
#check IsFractionRing.isAlgebraic_iff
#check IsFractionRing.isAlgebraic_iff' 
#check Algebra.IsAlgebraic.of_isIntegralClosure
#check IsIntegralClosure.isAlgebraic_iff
