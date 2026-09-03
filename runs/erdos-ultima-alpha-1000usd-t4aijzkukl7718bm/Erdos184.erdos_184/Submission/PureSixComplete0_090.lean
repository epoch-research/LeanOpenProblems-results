import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_90_0 : CompleteAt 90 0 := by decide +kernel
lemma complete_90_1 : CompleteAt 90 1 := by decide +kernel
lemma complete_90_2 : CompleteAt 90 2 := by decide +kernel
lemma complete_90_3 : CompleteAt 90 3 := by decide +kernel
lemma complete_case90 : ∀ e0, CompleteAt 90 e0 := by
  intro e0
  fin_cases e0
  · exact complete_90_0
  · exact complete_90_1
  · exact complete_90_2
  · exact complete_90_3
#print axioms complete_case90
end Erdos184Work.PureSixLocalFilter0
