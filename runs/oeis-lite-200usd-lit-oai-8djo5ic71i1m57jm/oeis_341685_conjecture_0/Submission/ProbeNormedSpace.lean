import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#synth NormedSpace ℚ (Padic 3)
#synth NormedSpace ℚ (PadicInt 3)
#check FiniteDimensional.of_locallyCompactSpace
#check FiniteDimensional.of_isCompact_closedBall
#check finiteDimensional_of_locallyCompactSpace
#check locallyCompactSpace_of_finiteDimensional
example : FiniteDimensional ℚ (Padic 3) := by
  apply?
