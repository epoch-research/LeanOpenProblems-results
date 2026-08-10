import FormalConjectures.Util.ProblemImports

#print Int.Linear.Context
#check Int.Linear.Context
#check (Lean.RArray.leaf (0:ℤ) : Int.Linear.Context)
#check (#[] : Array ℤ)
#check Int.Linear.Poly.denote'
#check Int.Linear.Poly.num
#eval Int.Linear.Poly.isUnsatDvd 2 (Int.Linear.Poly.num 1)
#eval Int.Linear.Poly.isUnsatDvd 2 (Int.Linear.Poly.num 0)
#eval Int.Linear.Poly.isUnsatDiseq_k (Int.Linear.Poly.num 0)
#eval Int.Linear.Poly.isUnsatDiseq_k (Int.Linear.Poly.num 1)

example : Int.Linear.Poly.isUnsatDvd 2 (Int.Linear.Poly.num 1) = true := rfl
example : Int.Linear.Poly.isUnsatDiseq_k (Int.Linear.Poly.num 0) = true := rfl

-- Try contradictions; these should fail on arithmetic side.
example : False := by
  refine Int.Linear.dvd_unsat (ctx := (Lean.RArray.leaf (0:ℤ) : Int.Linear.Context)) 2 (Int.Linear.Poly.num 1) rfl ?_
  norm_num [Int.Linear.Poly.denote']

example : False := by
  refine Int.Linear.diseq_unsat (ctx := (Lean.RArray.leaf (0:ℤ) : Int.Linear.Context)) (Int.Linear.Poly.num 0) rfl ?_
  norm_num [Int.Linear.Poly.denote']
