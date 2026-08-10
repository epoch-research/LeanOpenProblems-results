import Submission.Spec
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem t : checkRange 287 386 = true := by decide +kernel
#print axioms t
