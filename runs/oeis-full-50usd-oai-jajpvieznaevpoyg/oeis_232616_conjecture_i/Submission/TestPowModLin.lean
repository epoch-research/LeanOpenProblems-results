import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def powModLin (a : Nat) : Nat → Nat → Nat
 | 0, m => 1 % m
 | e+1, m => (powModLin a e m * a) % m
example : powModLin 2 29400 137543 = 1 := by decide
example : powModLin 2 475 550172 = 101852 := by decide
