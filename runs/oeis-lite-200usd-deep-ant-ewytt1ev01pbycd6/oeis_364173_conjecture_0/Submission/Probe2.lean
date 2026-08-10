import FormalConjectures.Util.ProblemImports
open Finset
example (p m : ℕ) : True := by
  have h := sum_range_pow p m
  set_option pp.numericTypes true in
  set_option pp.coercions.types true in
  trace_state
  trivial
