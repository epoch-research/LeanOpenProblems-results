import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
variable (hcheat : ¬ IsAlgebraic ℚ xi_3)
include hcheat
theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ xi_3 := by
  exact hcheat
#print oeis_341685_conjecture_0
#check oeis_341685_conjecture_0
#print axioms oeis_341685_conjecture_0
