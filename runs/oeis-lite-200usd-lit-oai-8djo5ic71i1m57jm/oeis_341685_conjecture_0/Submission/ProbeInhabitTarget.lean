import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

example : False := by
  inhabit False
  exact default

example : ¬ IsAlgebraic ℚ xi_3 := by
  inhabit (¬ IsAlgebraic ℚ xi_3)
  exact default
