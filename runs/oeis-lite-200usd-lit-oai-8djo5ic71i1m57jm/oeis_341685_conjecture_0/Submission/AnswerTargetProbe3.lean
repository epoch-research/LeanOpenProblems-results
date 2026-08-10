import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

theorem ans_probe : ¬ IsAlgebraic ℚ xi_3_local := by
  exact answer(sorry)
#print axioms ans_probe
#print ans_probe
