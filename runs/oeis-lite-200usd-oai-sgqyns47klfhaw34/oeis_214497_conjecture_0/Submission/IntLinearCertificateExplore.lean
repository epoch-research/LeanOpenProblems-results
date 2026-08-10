import FormalConjectures.Util.ProblemImports

#check Int.Linear.Poly.isUnsatDiseq_k
#print Int.Linear.Poly.isUnsatDiseq_k
#print Int.Linear.Poly.isUnsatDvd
#print Int.Linear.eq_unsat_coeff_cert
#print Int.Linear.cooper_unsat_cert

example : False := by
  refine Int.Linear.diseq_unsat (Lean.RArray.empty) (Int.Linear.Poly.num 0) ?_ ?_
  · native_decide
  · norm_num [Int.Linear.Poly.denote']

example : False := by
  refine Int.Linear.dvd_unsat (Lean.RArray.empty) 0 (Int.Linear.Poly.num 0) ?_ ?_
  · native_decide
  · exact dvd_zero 0

example : False := by
  refine Int.Linear.dvd_unsat (Lean.RArray.empty) 2 (Int.Linear.Poly.num 0) ?_ ?_
  · native_decide
  · exact dvd_zero 2
