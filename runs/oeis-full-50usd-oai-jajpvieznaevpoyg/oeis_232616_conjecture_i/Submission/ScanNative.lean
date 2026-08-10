import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 20000000

def N : Nat := 550172
def R : Nat := 13573

def scanNoR : Nat → Nat → Nat → Bool
  | k, 0, p => true
  | k, fuel+1, p =>
      (((p + N - (k % N)) % N) != R) && scanNoR (k+1) fuel ((p*2)%N)

#eval scanNoR 1 10 2

theorem scan_noR_true : scanNoR 1 16331503 2 = true := by
  native_decide
#print axioms scan_noR_true
