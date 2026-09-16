import Mathlib

set_option maxHeartbeats 0

def p : ℕ := 512720^2 + 21^2

def test : Nat.Prime p := by native_decide
