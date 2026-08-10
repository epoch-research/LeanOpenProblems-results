import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem lt1 : (UInt64.ofNat 5 < UInt64.ofNat 6) := by decide
#print axioms lt1

theorem le1 : (UInt64.ofNat 5 ≤ UInt64.ofNat 6) := by decide
#print axioms le1

theorem mod1 : (UInt64.ofNat 17) % (UInt64.ofNat 5) = UInt64.ofNat 2 := by decide
#print axioms mod1

theorem div1 : (UInt64.ofNat 17) / (UInt64.ofNat 5) = UInt64.ofNat 3 := by decide
#print axioms div1

theorem sub1 : (UInt64.ofNat 5) - (UInt64.ofNat 7) = UInt64.ofNat (2^64 - 2) := by decide
#print axioms sub1

def loopCmp : Nat -> UInt64 -> Bool
  | 0, x => true
  | n+1, x => if x % 3 = 0 then loopCmp n (x+1) else loopCmp n (x+2)

theorem loop1 : loopCmp 100 (UInt64.ofNat 0) = true := by decide
#print axioms loop1
