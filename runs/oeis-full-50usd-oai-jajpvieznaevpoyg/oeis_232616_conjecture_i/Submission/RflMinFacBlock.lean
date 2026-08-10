import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def isPrimeBool (n : Nat) : Bool := n.minFac == n && n != 1

def countBlockB : Nat → Nat → Nat
  | 0, lo => if isPrimeBool lo then 1 else 0
  | d+1, lo => countBlockB d lo + countBlockB d (lo + 2^d)

#eval countBlockB 9 8160000

theorem mb9hi_rfl : countBlockB 9 8160000 = 37 := rfl
#print axioms mb9hi_rfl
