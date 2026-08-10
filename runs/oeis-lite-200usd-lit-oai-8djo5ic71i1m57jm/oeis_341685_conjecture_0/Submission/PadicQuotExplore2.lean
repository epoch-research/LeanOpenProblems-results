import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

example : IsAlgebraic ℚ xi_3 := by
  unfold xi_3
  induction (tsum fun k : ℕ => (Nat.factorial k : Padic 3)) using Quot.ind with
  | mk f =>
    trace_state
    simp?
