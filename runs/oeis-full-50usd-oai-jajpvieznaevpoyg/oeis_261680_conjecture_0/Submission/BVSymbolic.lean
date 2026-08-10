import FormalConjectures.Util.ProblemImports

example (w : Nat) (x : BitVec w) : x + 0#w = x := by
  bv_decide

example (w : Nat) : ∀ x : BitVec w, x + 0#w = x := by
  intro x
  bv_decide
