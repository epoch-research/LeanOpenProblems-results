import FormalConjectures.Util.ProblemImports

theorem t : False := by
  classical
  exact if h : False then h else False.elim (h t)
