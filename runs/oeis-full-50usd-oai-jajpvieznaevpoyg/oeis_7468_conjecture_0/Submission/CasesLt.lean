import FormalConjectures.Util.ProblemImports
example (n : ℕ) (hn : 0 < n) : n = 38 := by
  cases hn
  case refl =>
    trace_state
    sorry
  case step a h =>
    trace_state
    sorry
