import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_102_0 : CompleteAt 102 0 := by decide +kernel
lemma complete_102_1 : CompleteAt 102 1 := by decide +kernel
lemma complete_102_2 : CompleteAt 102 2 := by decide +kernel
lemma complete_102_3 : CompleteAt 102 3 := by decide +kernel
lemma complete_case102 : ∀ e0, CompleteAt 102 e0 := by
  intro e0
  fin_cases e0
  · exact complete_102_0
  · exact complete_102_1
  · exact complete_102_2
  · exact complete_102_3
#print axioms complete_case102
end Erdos184Work.PureSixLocalFilter0
