import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Algebra.IsAlgebraic ℚ (Padic 3)
#synth IsAlgClosed (Padic 3)
#synth IsAlgClosure ℚ (Padic 3)
#synth Normal ℚ (Padic 3)
#synth Algebra.IsSeparable ℚ (Padic 3)
#synth FiniteDimensional ℚ (Padic 3)
#synth Module.Finite ℚ (Padic 3)
#synth Algebra.FiniteType ℚ (Padic 3)
#synth NumberField (Padic 3)
#synth Algebra.Transcendental ℚ (Padic 3)
#synth Module.Flat ℚ (Padic 3)
#synth Module.Free ℚ (Padic 3)
