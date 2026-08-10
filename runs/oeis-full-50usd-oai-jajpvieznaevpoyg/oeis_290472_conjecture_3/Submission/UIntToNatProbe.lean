import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem tn1 : (UInt64.ofNat 17).toNat = 17 := by decide
#print axioms tn1

def searchZSimple : Nat -> UInt64 -> UInt64 -> UInt64 -> Nat -> Bool
  | 0, N, k, z, cnt => cnt ≥ 2
  | f+1, N, k, z, cnt =>
    let zz := 7*z*z
    if zz > N then cnt ≥ 2 else searchZSimple f N k (z+1) (cnt+1)

theorem s1 : searchZSimple 100 (UInt64.ofNat 1000) 0 0 0 = true := by decide
#print axioms s1
