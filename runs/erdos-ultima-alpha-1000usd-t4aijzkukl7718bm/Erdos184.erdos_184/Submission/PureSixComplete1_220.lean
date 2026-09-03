import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_220_0 : CompleteAt 220 0 := by decide +kernel
lemma complete_220_1 : CompleteAt 220 1 := by decide +kernel
lemma complete_220_2 : CompleteAt 220 2 := by decide +kernel
lemma complete_220_3 : CompleteAt 220 3 := by decide +kernel
lemma complete_220_4 : CompleteAt 220 4 := by decide +kernel
lemma complete_case220 : ∀ e0, CompleteAt 220 e0 := by
  intro e0
  fin_cases e0
  · exact complete_220_0
  · exact complete_220_1
  · exact complete_220_2
  · exact complete_220_3
  · exact complete_220_4
#print axioms complete_case220
end Erdos184Work.PureSixLocalFilter1
