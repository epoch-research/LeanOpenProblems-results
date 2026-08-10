import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def isPrimeBool (n : Nat) : Bool := n.minFac == n && n != 1

def countBlock : Nat → Nat → Nat
  | 0, lo => if isPrimeBool lo then 1 else 0
  | d+1, lo => countBlock d lo + countBlock d (lo + 2^d)

theorem b12 : countBlock 12 0 = 564 := by decide
#print axioms b12

theorem b16 : countBlock 16 0 = 6542 := by decide
#print axioms b16
