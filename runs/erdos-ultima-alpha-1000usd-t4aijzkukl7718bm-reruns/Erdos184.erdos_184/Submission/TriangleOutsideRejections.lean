import Submission.TriangleOutsideBase

/-! Kernel verification of all saved pairs of disjoint cycles. -/
namespace Erdos184.TriangleOutsideData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma rejections_checked : rejections.all checkRejection = true := by
  decide +kernel

end Erdos184.TriangleOutsideData
