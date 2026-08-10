import FormalConjectures.Util.ProblemImports

#synth Algebra ℚ (Polynomial ℚ)
#synth Algebra.IsAlgebraic ℚ (Polynomial ℚ)
#synth Module.Finite ℚ (Polynomial ℚ)
#synth FiniteDimensional ℚ (Polynomial ℚ)

open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

noncomputable instance localEvalAlg : Algebra (Polynomial ℚ) (Padic 3) := (Polynomial.aeval xi_3).toRingHom.toAlgebra
#synth IsScalarTower ℚ (Polynomial ℚ) (Padic 3)
#synth Algebra.IsAlgebraic (Polynomial ℚ) (Padic 3)
#synth Algebra.IsAlgebraic ℚ (Padic 3)

example : IsAlgebraic ℚ xi_3 := by
  have hPX : IsAlgebraic (Polynomial ℚ) xi_3 := by
    -- likely X - C xi? coeff issue because coeff ring is polynomial Q, aeval into Padic with eval algebra
    sorry
  exact hPX.restrictScalars ℚ
