import Submission.CardinalitySieve
open Erdos7CardinalitySieve
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem threshold_test : thresholdCapacity ![3,5,7,11,13] ![5,3,2,1,1] 52 (1/420 : ℚ) < 1 := by
  decide +kernel
#print axioms threshold_test
