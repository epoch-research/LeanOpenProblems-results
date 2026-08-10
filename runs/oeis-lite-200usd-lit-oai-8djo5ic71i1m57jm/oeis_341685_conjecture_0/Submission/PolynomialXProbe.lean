import FormalConjectures.Util.ProblemImports
open Polynomial

noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#check Polynomial.transcendental_X (R := ℚ)
#check Transcendental.isAlgebraic_aeval_iff
#check Transcendental.of_aeval
#check Transcendental.aeval
#check IsAlgebraic.of_aeval

example : Transcendental ℚ (X : ℚ[X]) := Polynomial.transcendental_X
example : Polynomial.aeval xi_3_local (X : ℚ[X]) = xi_3_local := by simp

-- Try if exact known theorem can reduce target to itself
example : IsAlgebraic ℚ xi_3_local → IsAlgebraic ℚ xi_3_local := by
  intro h
  exact IsAlgebraic.of_aeval (r := xi_3_local) (f := (X : ℚ[X])) (by simpa using h) (Polynomial.transcendental_X (R := ℚ))
