import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_168_0 : CompleteAt 168 0 := by decide +kernel
lemma complete_168_1 : CompleteAt 168 1 := by decide +kernel
lemma complete_168_2 : CompleteAt 168 2 := by decide +kernel
lemma complete_168_3 : CompleteAt 168 3 := by decide +kernel
lemma complete_168_4 : CompleteAt 168 4 := by decide +kernel
lemma complete_case168 : ∀ e0, CompleteAt 168 e0 := by
  intro e0
  fin_cases e0
  · exact complete_168_0
  · exact complete_168_1
  · exact complete_168_2
  · exact complete_168_3
  · exact complete_168_4
#print axioms complete_case168
end Erdos184Work.PureSixLocalFilter1
