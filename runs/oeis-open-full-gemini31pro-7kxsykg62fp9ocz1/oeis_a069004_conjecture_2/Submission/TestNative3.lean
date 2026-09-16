import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun s => if Nat.Prime (n^2 + s^2) then 1 else 0

set_option maxHeartbeats 0
def test : a 512720 > Nat.primeCounting 512720 := by native_decide

