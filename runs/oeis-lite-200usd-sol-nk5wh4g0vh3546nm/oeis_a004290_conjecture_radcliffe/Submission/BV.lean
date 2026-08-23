import FormalConjectures.Util.ProblemImports

def decRemAux (n : BitVec 64) (x : BitVec 171) : ℕ → BitVec 64
  | 0 => 0
  | i+1 => (decRemAux n x i * 10 + if x.getLsbD i then 1 else 0) % n

def decRem (n : BitVec 64) (x : BitVec 171) : BitVec 64 := decRemAux n x 171

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
example (x : BitVec 171) (hx : x ≠ 0) :
    decRem 111 x ≠ 0 ∨ decRem 11111 x ≠ 0 ∨ decRem 1111111111111 x ≠ 0 := by
  simp only [decRem, decRemAux]
  bv_decide (config := { timeout := 3600 })
