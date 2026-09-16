import Mathlib
import Submission.Spec

set_option maxHeartbeats 0

def test : a 512720 = 42666 := by native_decide
