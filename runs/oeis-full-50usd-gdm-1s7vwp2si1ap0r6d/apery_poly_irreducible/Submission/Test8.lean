import FormalConjectures.Util.ProblemImports

open Nat

open Polynomial

lemma test (X : ℚ[X]) : (algebraMap ℚ ℚ[X]) 1 + (algebraMap ℚ ℚ[X]) 2 * X = 1 + X * 2 := by
  simp [C_ofNat]
  ring
