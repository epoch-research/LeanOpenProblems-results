import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 200000
#eval (UInt64.ofNat 1723) * (UInt64.ofNat 3)
theorem t1 : (UInt64.ofNat 1723) * (UInt64.ofNat 3) = UInt64.ofNat 5169 := by decide
#print axioms t1

def f (n : Nat) : UInt64 := UInt64.ofNat (6*n+1)
#eval f 287
theorem t2 : f 287 = UInt64.ofNat 1723 := by decide
#print axioms t2

def g (x y : UInt64) : Bool := (x*y + 3) == y
#eval g 7 52
theorem t3 : g 7 52 = false := by decide
#print axioms t3
