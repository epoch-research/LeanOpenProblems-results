import Submission.FiveWordOrbits1Base
/-! An ordinary-kernel five-word orbit certificate. -/
open scoped Classical
namespace Erdos184Work.FiveWordOrbits1
open LabelKernel Erdos184Serial CanonicalThreeReduction FiveRows1
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma edge_left_block1 : ∀ i : Fin 100, EdgeLeftProp (blockCase1 i) := by unfold EdgeLeftProp; decide +kernel
#print axioms edge_left_block1
end Erdos184Work.FiveWordOrbits1
