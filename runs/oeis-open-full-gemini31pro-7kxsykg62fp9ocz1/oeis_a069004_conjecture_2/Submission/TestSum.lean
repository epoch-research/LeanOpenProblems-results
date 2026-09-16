import Mathlib

set_option maxHeartbeats 0

def test : (Finset.Ico 1 512720).sum (fun s => 1) = 512719 := by native_decide
