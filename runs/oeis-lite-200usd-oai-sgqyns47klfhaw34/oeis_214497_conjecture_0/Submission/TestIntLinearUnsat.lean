import FormalConjectures.Util.ProblemImports

#eval Int.Linear.Poly.isUnsatLe (Int.Linear.Poly.num 1)
#eval Int.Linear.Poly.isUnsatEq (Int.Linear.Poly.num 1)
#eval Int.Linear.Poly.isUnsatDiseq_k (Int.Linear.Poly.num 0)
#eval Int.Linear.Poly.isUnsatDvd 0 (Int.Linear.Poly.num 1)
#eval Int.Linear.Poly.isUnsatDvd 2 (Int.Linear.Poly.num 1)

example : False := by
  refine Int.Linear.le_unsat default (Int.Linear.Poly.num 1) ?_ ?_
  · native_decide
  · norm_num
