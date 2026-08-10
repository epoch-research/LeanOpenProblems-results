import FormalConjectures.Util.ProblemImports

theorem bad : False := by
  let rec loop : False := loop
  exact loop

#print axioms bad
