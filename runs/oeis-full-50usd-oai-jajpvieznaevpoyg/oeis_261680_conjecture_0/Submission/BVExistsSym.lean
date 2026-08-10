import FormalConjectures.Util.ProblemImports

example (w : Nat) (x : BitVec w) : ∃ u v : BitVec w, u + v = x := by
  bv_decide
