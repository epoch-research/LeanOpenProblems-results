import FormalConjectures.Util.ProblemImports
opaque badProp : False
#print axioms badProp
opaque badProp2 : False := by
  exact badProp
#print axioms badProp2
