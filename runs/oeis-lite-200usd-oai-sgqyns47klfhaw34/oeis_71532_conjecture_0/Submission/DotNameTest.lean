import FormalConjectures.Util.ProblemImports

theorem foo.disproof : ¬ True := by
  intro h
  exact False.elim (by contradiction)
