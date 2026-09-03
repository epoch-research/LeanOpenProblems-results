import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_243_0 : CompleteAt 243 0 := by decide +kernel
lemma complete_243_1 : CompleteAt 243 1 := by decide +kernel
lemma complete_243_2 : CompleteAt 243 2 := by decide +kernel
lemma complete_243_3 : CompleteAt 243 3 := by decide +kernel
lemma complete_243_4 : CompleteAt 243 4 := by decide +kernel
lemma complete_case243 : ∀ e0, CompleteAt 243 e0 := by
  intro e0
  fin_cases e0
  · exact complete_243_0
  · exact complete_243_1
  · exact complete_243_2
  · exact complete_243_3
  · exact complete_243_4
#print axioms complete_case243
end Erdos184Work.PureSixLocalFilter1
