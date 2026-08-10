import FormalConjectures.Util.ProblemImports
#print Int.Linear.Poly
#print Int.Linear.Context
#print Int.Linear.Var
#check Int.Linear.Poly.num
#check Int.Linear.Poly.add
#eval Int.Linear.Poly.isUnsatDvd 0 (.num 0)
#eval Int.Linear.Poly.isUnsatDvd 1 (.num 0)
#eval Int.Linear.Poly.isUnsatDvd 2 (.num 1)
#eval Int.Linear.Poly.isUnsatEq (.num 1)
#eval Int.Linear.Poly.isUnsatEq (.num 0)
