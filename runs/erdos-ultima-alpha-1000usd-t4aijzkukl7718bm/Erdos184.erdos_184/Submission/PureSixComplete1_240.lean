import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_240_0 : CompleteAt 240 0 := by decide +kernel
lemma complete_240_1 : CompleteAt 240 1 := by decide +kernel
lemma complete_240_2 : CompleteAt 240 2 := by decide +kernel
lemma complete_240_3 : CompleteAt 240 3 := by decide +kernel
lemma complete_240_4 : CompleteAt 240 4 := by decide +kernel
lemma complete_case240 : ∀ e0, CompleteAt 240 e0 := by
  intro e0
  fin_cases e0
  · exact complete_240_0
  · exact complete_240_1
  · exact complete_240_2
  · exact complete_240_3
  · exact complete_240_4
#print axioms complete_case240
end Erdos184Work.PureSixLocalFilter1
