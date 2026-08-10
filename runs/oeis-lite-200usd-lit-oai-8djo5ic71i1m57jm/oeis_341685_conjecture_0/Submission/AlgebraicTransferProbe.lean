import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

#check Algebra.IsAlgebraic.of_injective
#check Algebra.IsAlgebraic.of_ringHom_of_comp_eq
#check IsAlgebraic.of_ringHom_of_comp_eq
#check IsAlgebraic.of_finite
#check Algebra.IsAlgebraic.of_finite
#check IsIntegral.of_finite
#check IsIntegral.isAlgebraic
#check IsAlgebraic.of_aeval

example : IsAlgebraic ℚ xi_3 := by
  -- try likely transfer/finite lemmas without extra assumptions
  first
  | exact IsAlgebraic.of_finite ℚ xi_3
  | exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A := Padic 3) xi_3)
