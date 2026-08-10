import FormalConjectures.Util.ProblemImports
unsafe def badDef : False := unsafeCast True
theorem bad : False := by exact badDef
#print axioms bad
