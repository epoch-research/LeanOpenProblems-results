import Submission.FiveWordOrbits1Base
/-! An ordinary-kernel five-word orbit certificate. -/
open scoped Classical
namespace Erdos184Work.FiveWordOrbits1
open LabelKernel Erdos184Serial CanonicalThreeReduction FiveRows1
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma endpoints_valid_block0 : ∀ i : Fin 100, EndpointsProp (blockCase0 i) := by unfold EndpointsProp; decide +kernel
#print axioms endpoints_valid_block0
end Erdos184Work.FiveWordOrbits1
