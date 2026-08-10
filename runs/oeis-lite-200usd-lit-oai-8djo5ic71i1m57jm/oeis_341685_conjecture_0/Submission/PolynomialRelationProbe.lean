import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra Polynomial

#synth Nontrivial (Padic 3)
#synth CharZero (Padic 3)
#synth NoZeroSMulDivisors ℚ (Padic 3)
#check isAlgebraic_iff_isIntegral
#check Polynomial.aeval_X
#check Polynomial.aeval_C
#check Polynomial.aeval_X_sub_C

example : Polynomial.aeval xi_3 (Polynomial.X : Polynomial ℚ) = xi_3 := by simp
example : Polynomial.aeval xi_3 (1 : Polynomial ℚ) = (1 : Padic 3) := by simp
example : (1 : Polynomial ℚ) ≠ 0 := by norm_num
example : Polynomial.aeval xi_3 (1 : Polynomial ℚ) ≠ (0 : Padic 3) := by norm_num

example : IsAlgebraic ℚ (xi_3) := by
  unfold IsAlgebraic
  refine ⟨(1 : Polynomial ℚ), by norm_num, ?_⟩
  norm_num
