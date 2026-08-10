import FormalConjectures.Util.ProblemImports
example (w : Nat) (x : BitVec w) : ∃ y : BitVec w, x = y := by
  bv_decide
