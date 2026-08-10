import FormalConjectures.Util.ProblemImports
open Int.Linear
#eval (Poly.add 1 0 (.num 1)).isUnsatLe
#eval (Poly.add (-1) 0 (.num 1)).isUnsatLe
#eval (Poly.add 0 0 (.num 1)).isUnsatLe
#reduce Poly.denote' (Lean.RArray.leaf (-1)) (Poly.add 1 0 (.num 1))
example : False := by
  refine Int.Linear.le_unsat (Lean.RArray.leaf (-1)) (Poly.add 1 0 (.num 1)) ?_ ?_
  · native_decide
  · norm_num [Int.Linear.Poly.denote', Int.Linear.Poly.denote, Int.Linear.Var.denote]
