import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

theorem ans_target2 : ¬ IsAlgebraic ℚ xi_3_local := by
  exact answer(sorry)
#print axioms ans_target2
#print ans_target2
