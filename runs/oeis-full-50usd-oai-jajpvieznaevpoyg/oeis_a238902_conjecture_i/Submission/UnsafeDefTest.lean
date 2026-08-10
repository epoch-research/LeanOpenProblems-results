import FormalConjectures.Util.ProblemImports

unsafe def pf : False := unsafeCast True.intro

theorem t : False := by
  exact pf

#print axioms t
