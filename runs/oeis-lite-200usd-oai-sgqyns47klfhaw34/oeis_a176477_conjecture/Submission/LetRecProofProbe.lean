import FormalConjectures.Util.ProblemImports

theorem bad1 : False := by
  let rec loop : False := loop
  exact loop

#print axioms bad1
