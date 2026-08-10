import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
example : ¬ IsAlgebraic ℚ xi_3 := by
  change answer(sorry)
  trivial
example : ¬ IsAlgebraic ℚ xi_3 := by
  show answer(sorry)
  trivial
