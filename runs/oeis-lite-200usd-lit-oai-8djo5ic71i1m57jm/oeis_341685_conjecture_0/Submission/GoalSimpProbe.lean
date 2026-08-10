import FormalConjectures.Util.ProblemImports

open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

example : ¬ IsAlgebraic ℚ (xi_3) := by
  unfold IsAlgebraic
  simp only [not_exists, not_and]
  intro p hp
  -- show available? 
  guard_target = Polynomial.aeval xi_3 p ≠ 0
  sorry

#check Algebra.transcendental_iff_not_isAlgebraic
#check Algebra.Transcendental
#check IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero
#check IsAlgebraic.exists_aeval_eq_zero
#check Padic.denseRange_ratCast
#check Padic.ext
#check Padic.eq_padicNorm
#check Padic.norm_rat
#check Padic.valuation_ratCast
