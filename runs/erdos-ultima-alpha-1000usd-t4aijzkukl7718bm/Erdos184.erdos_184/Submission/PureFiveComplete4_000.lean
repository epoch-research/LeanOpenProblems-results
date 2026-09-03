import Submission.PureFiveComplete4Base

/-! Factored kernel coverage for one value of the distinguished row key. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma ordered_0 : OrderedComplete 0 := by decide +kernel
#print axioms ordered_0
end Erdos184Work.PureFiveFilter4
