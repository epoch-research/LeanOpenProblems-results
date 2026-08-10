import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check CauSeq.Completion.Cauchy.ind
#print CauSeq.Completion.Cauchy.ind
#check CauSeq.Completion.ind
#check Padic

example : IsAlgebraic ℚ xi_3 := by
  unfold xi_3
  induction (tsum fun k : ℕ => (Nat.factorial k : Padic 3)) using CauSeq.Completion.Cauchy.ind with
  | h f =>
    trace_state
    exact isAlgebraic_zero
