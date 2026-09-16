import Mathlib

set_option maxHeartbeats 0

def f (s : ℕ) : ℕ := if Nat.Prime (512720^2 + s^2) then 1 else 0

def test1 : (Finset.Ico 1 100000).sum f = 7711 := by native_decide
