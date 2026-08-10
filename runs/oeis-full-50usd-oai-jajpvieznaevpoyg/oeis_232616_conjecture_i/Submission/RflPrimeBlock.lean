import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def countBlockP : Nat → Nat → Nat
  | 0, lo => if Nat.Prime lo then 1 else 0
  | d+1, lo => countBlockP d lo + countBlockP d (lo + 2^d)

theorem pb9hi_rfl : countBlockP 9 8160000 = 37 := rfl
#print axioms pb9hi_rfl
