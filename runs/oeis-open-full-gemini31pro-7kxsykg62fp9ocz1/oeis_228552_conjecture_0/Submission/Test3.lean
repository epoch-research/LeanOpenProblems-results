import Submission.Spec
open Matrix Nat

set_option maxRecDepth 20000000
set_option maxHeartbeats 20000000

theorem a_16_pos : a 16 > 0 := by
  decide
