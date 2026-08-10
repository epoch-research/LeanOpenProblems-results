import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 20000000

open Finset ZMod Nat Set Classical

def powMod (a e m : Nat) : Nat :=
  match e with
  | 0 => 1 % m
  | e+1 =>
      let r := powMod ((a*a)%m) ((e+1)/2) m
      if (e+1) % 2 = 0 then r else (r*a)%m
termination_by e

def NN : Nat := 550172
def RR : Nat := 13573
def BB : Nat := 16331504

def residueAt (k : Nat) : Nat := ((powMod 2 k NN + NN - (k % NN)) % NN)

def scanNoRFull : Nat → Nat → Bool
  | k, 0 => true
  | k, fuel+1 => (residueAt k != RR) && scanNoRFull (k+1) fuel

#eval scanNoRFull 1 10
theorem scanNoRFull_true : scanNoRFull 1 16331503 = true := by native_decide
#print axioms scanNoRFull_true
