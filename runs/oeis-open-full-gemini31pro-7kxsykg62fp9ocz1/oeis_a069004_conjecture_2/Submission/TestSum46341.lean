import Mathlib

set_option maxHeartbeats 0

def test : (Finset.Ico 1 46341).sum (fun s => 1) = 46340 := by native_decide
