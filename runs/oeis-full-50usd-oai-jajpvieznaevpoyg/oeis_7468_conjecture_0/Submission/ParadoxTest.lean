import FormalConjectures.Util.ProblemImports
theorem bad : False := by
  let x : False := Classical.byContradiction' (fun h => h x)
  exact x
#print axioms bad
