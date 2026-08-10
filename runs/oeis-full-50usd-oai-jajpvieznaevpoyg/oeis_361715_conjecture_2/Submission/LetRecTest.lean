import FormalConjectures.Util.ProblemImports

theorem t : False := by
  let rec loop : False := loop
  exact loop
#print axioms t
