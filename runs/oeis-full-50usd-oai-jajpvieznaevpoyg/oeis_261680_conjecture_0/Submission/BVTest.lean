import FormalConjectures.Util.ProblemImports
example (w : Nat) (x : BitVec w) : x = x := by
  bv_decide
