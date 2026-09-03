import Submission.TriangleOutsideBase

/-! Kernel verification of one normalized degree case. -/
namespace Erdos184.TriangleOutsideData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma range_checked_1_2 : checkRange 1 2 10 0 = true := by
  decide +kernel

lemma range_checked_1_3 : checkRange 1 3 10 0 = true := by
  decide +kernel

lemma range_checked_1_4 : checkRange 1 4 10 0 = true := by
  decide +kernel

lemma range_checked_1_5 : checkRange 1 5 10 0 = true := by
  decide +kernel

lemma range_checked_1_6 : checkRange 1 6 10 0 = true := by
  decide +kernel

end Erdos184.TriangleOutsideData
