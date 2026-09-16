import Mathlib

set_option maxHeartbeats 0

def test1 : Nat.primeCounting 512720 = 42493 := by native_decide

