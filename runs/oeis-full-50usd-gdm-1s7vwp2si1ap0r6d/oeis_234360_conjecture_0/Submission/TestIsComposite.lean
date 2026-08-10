import Submission.Spec

set_option exponentiation.threshold 10000
set_option maxRecDepth 150000

theorem test_comp : OEIS234360.isComposite 84 = true := by decide


