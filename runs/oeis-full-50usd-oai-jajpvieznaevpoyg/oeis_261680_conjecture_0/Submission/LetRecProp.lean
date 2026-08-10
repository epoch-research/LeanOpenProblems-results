import FormalConjectures.Util.ProblemImports
theorem bad : False := by
  let rec f : False := f
  exact f
#print axioms bad
