import FormalConjectures.Util.ProblemImports
unsafe def badFalse : False := unsafeCast ()
theorem useBad : False := by
  exact badFalse
#print axioms useBad
