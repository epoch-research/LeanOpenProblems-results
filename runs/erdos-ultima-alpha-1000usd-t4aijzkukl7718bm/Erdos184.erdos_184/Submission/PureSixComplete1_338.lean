import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_338_0 : CompleteAt 338 0 := by decide +kernel
lemma complete_338_1 : CompleteAt 338 1 := by decide +kernel
lemma complete_338_2 : CompleteAt 338 2 := by decide +kernel
lemma complete_338_3 : CompleteAt 338 3 := by decide +kernel
lemma complete_338_4 : CompleteAt 338 4 := by decide +kernel
lemma complete_case338 : ∀ e0, CompleteAt 338 e0 := by
  intro e0
  fin_cases e0
  · exact complete_338_0
  · exact complete_338_1
  · exact complete_338_2
  · exact complete_338_3
  · exact complete_338_4
#print axioms complete_case338
end Erdos184Work.PureSixLocalFilter1
