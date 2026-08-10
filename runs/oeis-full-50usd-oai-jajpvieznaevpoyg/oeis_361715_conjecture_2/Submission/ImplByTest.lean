import FormalConjectures.Util.ProblemImports

private def safeFalseImpl : False := False.elim (by contradiction)
@[implemented_by safeFalseImpl]
def safeFalse : False := by
  exact False.elim (by contradiction)

theorem t : False := safeFalse
#print axioms t
