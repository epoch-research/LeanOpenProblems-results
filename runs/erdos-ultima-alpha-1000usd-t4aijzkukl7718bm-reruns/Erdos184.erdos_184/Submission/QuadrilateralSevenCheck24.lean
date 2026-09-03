import Submission.QuadrilateralOutsideData

/-! One kernel-checked block of the single-root seven-vertex classification. -/
namespace Erdos184.QuadrilateralOutsideData
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
lemma seven_block_24 : checkRange 7 10 24576 = true := by
  decide +kernel
end Erdos184.QuadrilateralOutsideData
