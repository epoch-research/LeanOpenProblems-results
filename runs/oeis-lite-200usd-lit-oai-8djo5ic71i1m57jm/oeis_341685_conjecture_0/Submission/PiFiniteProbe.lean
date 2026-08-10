import FormalConjectures.Util.ProblemImports
#synth Module.Finite ℚ (ℚ → ℚ)
#synth FiniteDimensional ℚ (ℚ → ℚ)
#synth Algebra.IsAlgebraic ℚ (ℚ → ℚ)
example : Module.Finite ℚ (ℚ → ℚ) := by infer_instance
example : IsAlgebraic ℚ (fun q : ℚ => q) := by exact IsAlgebraic.of_finite ℚ _
