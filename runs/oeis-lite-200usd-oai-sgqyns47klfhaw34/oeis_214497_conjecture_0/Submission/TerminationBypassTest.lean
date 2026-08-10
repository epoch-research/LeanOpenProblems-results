import FormalConjectures.Util.ProblemImports

theorem bad_same (n : ℕ) : False := by
  exact bad_same n
termination_by n

theorem bad_bigger (n : ℕ) : False := by
  exact bad_bigger (n+1)
termination_by n
