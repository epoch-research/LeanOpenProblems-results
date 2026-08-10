import FormalConjectures.Util.ProblemImports
#check FormalConjecturesForMathlib
#check Polynomial.instAlgebraPi
#synth Algebra ℚ[X] (ℚ → ℚ)
#check algebraMap ℚ[X] (ℚ → ℚ)
#check IsAlgebraic ℚ[X] (fun x : ℚ => x)
example : IsAlgebraic ℚ[X] (fun x : ℚ => x) := by
  apply?
example : ¬ IsAlgebraic ℚ[X] (fun x : ℚ => x) := by
  apply?
