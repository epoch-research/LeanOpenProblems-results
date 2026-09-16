import Submission.Spec
open Nat

set_option maxRecDepth 200000000
set_option maxHeartbeats 200000000

theorem test : primeCounting 200 = 46 := by decide
