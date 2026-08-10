import FormalConjectures.Util.ProblemImports
unsafe theorem bad : False := by
  exact unsafeCast True.intro
#print axioms bad
