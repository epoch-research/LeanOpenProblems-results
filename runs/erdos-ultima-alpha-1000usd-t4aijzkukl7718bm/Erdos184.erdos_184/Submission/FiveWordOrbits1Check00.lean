import Submission.FiveWordOrbits1Base
/-! An ordinary-kernel five-word orbit certificate. -/
open scoped Classical
namespace Erdos184Work.FiveWordOrbits1
open LabelKernel Erdos184Serial CanonicalThreeReduction FiveRows1
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma good_eq : FiveRows1.good = Finset.univ.image caseKey := by decide +kernel
#print axioms good_eq
end Erdos184Work.FiveWordOrbits1
