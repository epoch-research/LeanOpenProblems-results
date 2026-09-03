import Submission.TriangleOutsideBase

/-! Kernel verification of one normalized degree case. -/
namespace Erdos184.TriangleOutsideData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma range_checked_2_2 : checkRange 2 2 10 0 = true := by
  decide +kernel

lemma range_checked_2_3 : checkRange 2 3 10 0 = true := by
  decide +kernel

lemma range_checked_2_4 : checkRange 2 4 10 0 = true := by
  decide +kernel

lemma range_checked_2_5 : checkRange 2 5 10 0 = true := by
  decide +kernel

lemma range_checked_2_6 : checkRange 2 6 10 0 = true := by
  decide +kernel

end Erdos184.TriangleOutsideData
