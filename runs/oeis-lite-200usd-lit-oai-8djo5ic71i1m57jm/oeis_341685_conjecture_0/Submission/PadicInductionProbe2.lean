import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
set_option pp.all true
example (x : Padic 3) : IsAlgebraic ℚ x := by
  refine Quot.ind ?_ x
  intro f
  trace_state
  sorry
