import FormalConjectures.Util.ProblemImports

example : False := by
  let rec bad : False := bad
  exact bad

example : False :=
  let rec bad : False := bad
  bad

unsafe def ubad : False := ubad
#print axioms ubad
