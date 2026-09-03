import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_394_0 : CompleteAt 394 0 := by decide +kernel
lemma complete_394_1 : CompleteAt 394 1 := by decide +kernel
lemma complete_394_2 : CompleteAt 394 2 := by decide +kernel
lemma complete_394_3 : CompleteAt 394 3 := by decide +kernel
lemma complete_394_4 : CompleteAt 394 4 := by decide +kernel
lemma complete_case394 : ∀ e0, CompleteAt 394 e0 := by
  intro e0
  fin_cases e0
  · exact complete_394_0
  · exact complete_394_1
  · exact complete_394_2
  · exact complete_394_3
  · exact complete_394_4
#print axioms complete_case394
end Erdos184Work.PureSixLocalFilter1
