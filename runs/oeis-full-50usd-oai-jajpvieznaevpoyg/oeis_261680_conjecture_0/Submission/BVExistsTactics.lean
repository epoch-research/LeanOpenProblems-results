import FormalConjectures.Util.ProblemImports

example (w : Nat) (x : BitVec w) : ∃ u v : BitVec w, u + v = x := by
  exists x, 0#w
  bv_decide

-- Check names
#check bv_decide
#check omega
#check decide
#check native_decide
