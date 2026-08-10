import FormalConjectures.Util.ProblemImports

def bad1 : False := by
  let rec f : False := f
  exact f

def bad2 : False :=
  let rec f : False := f
  f
