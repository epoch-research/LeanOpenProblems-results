import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun s => if Nat.Prime (n^2 + s^2) then 1 else 0

set_option maxHeartbeats 0

def test1 : a 46341 = 1861 := by native_decide
def test2 : Nat.primeCounting 46341 = 4792 := by native_decide

