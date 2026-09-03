import Submission.TriangleOutsideBase

/-! Kernel verification of one normalized degree case. -/
namespace Erdos184.TriangleOutsideData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma range_checked_3_2 : checkRange 3 2 10 0 = true := by
  decide +kernel

lemma range_checked_3_3 : checkRange 3 3 10 0 = true := by
  decide +kernel

lemma range_checked_3_4 : checkRange 3 4 10 0 = true := by
  decide +kernel

lemma range_checked_3_5 : checkRange 3 5 10 0 = true := by
  decide +kernel

lemma range_checked_3_6 : checkRange 3 6 10 0 = true := by
  decide +kernel

end Erdos184.TriangleOutsideData
