import FormalConjectures.Util.ProblemImports
theorem bad : False := by
  let rec x : False := x
  exact x
#print axioms bad
