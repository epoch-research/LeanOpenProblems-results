import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
#check IsAlgebraic
#check isAlgebraic_iff_isIntegral
#check Algebra.transcendental_iff_not_isAlgebraic
example : (IsAlgebraic ℚ xi_3) = _ := rfl
#print IsAlgebraic
#print IsIntegral
set_option pp.all true in
#check (show ¬ IsAlgebraic ℚ xi_3 from by intro h; exact False.elim (by cases h))
