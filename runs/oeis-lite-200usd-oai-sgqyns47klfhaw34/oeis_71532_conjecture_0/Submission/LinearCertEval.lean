import FormalConjectures.Util.ProblemImports
open Int.Linear
#eval Poly.isUnsatEq (.num 0)
#eval Poly.isUnsatEq (.num 1)
#eval Poly.isUnsatLe (.num 0)
#eval Poly.isUnsatLe (.num 1)
#eval Poly.isUnsatLe (.num (-1))
#eval Poly.denote' (Lean.RArray.leaf) (.num 0)
#eval Poly.denote' (Lean.RArray.leaf) (.num 1)
example : False := by
  exact Int.Linear.eq_unsat Lean.RArray.leaf (.num 0) (by native_decide) (by native_decide)
