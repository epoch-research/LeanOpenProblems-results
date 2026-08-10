import FormalConjectures.Util.ProblemImports

set_option pp.all true
example : True := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have hfield : (0 : ℕ) ≠ (1 : ℕ) := zero_ne_one
  trace_state
  trivial
