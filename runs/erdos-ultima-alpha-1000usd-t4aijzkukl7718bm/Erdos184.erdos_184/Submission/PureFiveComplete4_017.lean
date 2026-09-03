import Submission.PureFiveComplete4Base

/-! Factored kernel coverage for one value of the distinguished row key. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma ordered_17 : OrderedComplete 17 := by decide +kernel
#print axioms ordered_17
end Erdos184Work.PureFiveFilter4
