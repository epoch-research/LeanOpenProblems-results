import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check (DivisionRing.toRatAlgebra (R := Padic 3))[xi_3]?
set_option pp.all true
#check (show (DivisionRing.toRatAlgebra (R := Padic 3))[xi_3]? = none ↔ ¬ IsAlgebraic ℚ xi_3 from getElem?_eq_none_iff (DivisionRing.toRatAlgebra (R := Padic 3)) xi_3)
example : ¬ IsAlgebraic ℚ xi_3 := by
  rw [← getElem?_eq_none_iff (DivisionRing.toRatAlgebra (R := Padic 3)) xi_3]
  exact?
