import FormalConjectures.Util.ProblemImports
open Int.Linear

def ctx0 : Context := Lean.RArray.leaf 0

def polys : List Poly := [Poly.num (-2), Poly.num (-1), Poly.num 0, Poly.num 1, Poly.num 2,
  Poly.add (-2) 0 (.num 0), Poly.add (-1) 0 (.num 0), Poly.add 0 0 (.num 0), Poly.add 1 0 (.num 0), Poly.add 2 0 (.num 0),
  Poly.add 1 0 (.num (-1)), Poly.add 1 0 (.num 1), Poly.add (-1) 0 (.num 1)]

#eval polys.map (fun p => (p.isUnsatEq, p.isUnsatLe, p.denote' ctx0))

-- Try one if suspicious manually later
example : False := by
  norm_num
