import Submission.WitnessAuto
open Nat Finset
example : A308934 444926110 > 0 := by
  -- 444926110 = 162² + 2² + 21070² + 2·691²; 162=2^1*3^4, 2=2^1*3^0
  exact A308934_pos_of_witness 444926110 1 4 1 0 21070 691 (by decide) (by norm_num)
#print axioms _example
