import Submission.QuadrilateralOutsideData

/-! One kernel-checked block of the single-root seven-vertex classification. -/
namespace Erdos184.QuadrilateralOutsideData
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
lemma seven_block_15 : checkRange 7 10 15360 = true := by
  decide +kernel
end Erdos184.QuadrilateralOutsideData
