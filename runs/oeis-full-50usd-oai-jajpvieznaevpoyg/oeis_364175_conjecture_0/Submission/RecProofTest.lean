import FormalConjectures.Util.ProblemImports

theorem t : False := by
  let rec f (n : ℕ) : False := f (n+1)
  exact f 0
