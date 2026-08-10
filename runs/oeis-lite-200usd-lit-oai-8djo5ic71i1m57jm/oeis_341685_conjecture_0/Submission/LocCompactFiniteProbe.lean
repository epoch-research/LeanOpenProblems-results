import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check FiniteDimensional.of_locallyCompactSpace
#check FiniteDimensional.proper_rclike
#synth NormedSpace ℚ (Padic 3)
#synth LocallyCompactSpace (Padic 3)
#synth LocallyCompactSpace ℚ
#synth ProperSpace (Padic 3)
#synth ProperSpace ℚ
example : FiniteDimensional ℚ (Padic 3) := by
  exact FiniteDimensional.of_locallyCompactSpace (𝕜 := ℚ) (E := Padic 3)
example : IsAlgebraic ℚ (tsum (fun k : ℕ => (Nat.factorial k : Padic 3))) := by
  haveI : Module.Finite ℚ (Padic 3) := FiniteDimensional.finiteDimensional
  exact IsAlgebraic.of_finite ℚ _
