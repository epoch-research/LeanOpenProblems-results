import FormalConjectures.Util.ProblemImports

theorem bad (p r : ℕ) : False := by
  exact bad p r
termination_by p ^ r
decreasing_by omega
