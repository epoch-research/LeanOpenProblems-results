import Submission.TestFastKernel

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem test_one : a_fast_opt 6678671 = 14 := by decide
