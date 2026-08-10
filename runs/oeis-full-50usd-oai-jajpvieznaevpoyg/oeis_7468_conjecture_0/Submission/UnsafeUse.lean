import FormalConjectures.Util.ProblemImports

unsafe def badUnsafe : False := unsafeCast ()

theorem bad : False := by
  exact badUnsafe
#print axioms bad
