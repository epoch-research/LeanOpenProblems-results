import FormalConjectures.Util.ProblemImports

#check Int.Linear.dvd_unsat
#check Int.Linear.Poly.nil
#check Int.Linear.Poly.isUnsatDvd
#check Int.Linear.Poly.denote'
#check Int.Linear.Context
#eval Int.Linear.Poly.isUnsatDvd 0 Int.Linear.Poly.nil
#eval Int.Linear.Poly.isUnsatDvd 1 Int.Linear.Poly.nil
#eval Int.Linear.Poly.isUnsatEq Int.Linear.Poly.nil

example : False := by
  apply Int.Linear.dvd_unsat (ctx := {}) (k := 0) (p := Int.Linear.Poly.nil)
  · native_decide
  · simp [Int.Linear.Poly.denote']
