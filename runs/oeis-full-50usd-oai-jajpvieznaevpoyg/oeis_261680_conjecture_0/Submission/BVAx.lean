import FormalConjectures.Util.ProblemImports
theorem t (x y : BitVec 8) : x + y = y + x := by
  bv_decide
#print axioms t
