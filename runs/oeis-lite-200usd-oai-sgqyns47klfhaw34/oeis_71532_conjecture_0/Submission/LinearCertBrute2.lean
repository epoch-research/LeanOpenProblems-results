import FormalConjectures.Util.ProblemImports
open Int.Linear

def ctx0 : Context := Lean.RArray.leaf 0
#eval (Poly.add 1 0 (.num 0)).isUnsatEq
#eval (Poly.add 1 0 (.num (-1))).isUnsatEq
#eval (Poly.add 2 0 (.num 0)).isUnsatEq
#eval (Poly.add 2 0 (.num 1)).isUnsatEq
#reduce Poly.denote' ctx0 (Poly.add 1 0 (.num 0))
#reduce Poly.denote' ctx0 (Poly.add 1 0 (.num (-1)))

example : False := by
  refine Int.Linear.eq_unsat ctx0 (Poly.add 1 0 (.num 0)) ?_ ?_
  · native_decide
  · simp [ctx0, Int.Linear.Poly.denote']
