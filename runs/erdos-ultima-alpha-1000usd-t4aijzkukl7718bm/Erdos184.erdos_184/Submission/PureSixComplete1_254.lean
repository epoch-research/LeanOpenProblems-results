import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_254_0 : CompleteAt 254 0 := by decide +kernel
lemma complete_254_1 : CompleteAt 254 1 := by decide +kernel
lemma complete_254_2 : CompleteAt 254 2 := by decide +kernel
lemma complete_254_3 : CompleteAt 254 3 := by decide +kernel
lemma complete_254_4 : CompleteAt 254 4 := by decide +kernel
lemma complete_case254 : ∀ e0, CompleteAt 254 e0 := by
  intro e0
  fin_cases e0
  · exact complete_254_0
  · exact complete_254_1
  · exact complete_254_2
  · exact complete_254_3
  · exact complete_254_4
#print axioms complete_case254
end Erdos184Work.PureSixLocalFilter1
