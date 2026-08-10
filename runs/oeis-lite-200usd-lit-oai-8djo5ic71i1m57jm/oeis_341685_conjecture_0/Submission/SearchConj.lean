import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_test : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

example : IsAlgebraic ℚ (xi_3_test) := by
  exact?

example : ¬ IsAlgebraic ℚ (xi_3_test) := by
  exact?
