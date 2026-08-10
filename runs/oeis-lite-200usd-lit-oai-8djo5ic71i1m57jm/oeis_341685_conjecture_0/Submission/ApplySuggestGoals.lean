import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
set_option maxHeartbeats 800000
example : IsAlgebraic ℚ (xi_3) := by
  apply?
example : ¬ IsAlgebraic ℚ (xi_3) := by
  apply?
example : ¬ (¬ IsAlgebraic ℚ (xi_3)) := by
  apply?
example : Module.Finite ℚ (Padic 3) := by
  apply?
example : Algebra.IsAlgebraic ℚ (Padic 3) := by
  apply?
