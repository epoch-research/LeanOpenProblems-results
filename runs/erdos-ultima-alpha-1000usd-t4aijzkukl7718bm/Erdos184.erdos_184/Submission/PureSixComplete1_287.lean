import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_287_0 : CompleteAt 287 0 := by decide +kernel
lemma complete_287_1 : CompleteAt 287 1 := by decide +kernel
lemma complete_287_2 : CompleteAt 287 2 := by decide +kernel
lemma complete_287_3 : CompleteAt 287 3 := by decide +kernel
lemma complete_287_4 : CompleteAt 287 4 := by decide +kernel
lemma complete_case287 : ∀ e0, CompleteAt 287 e0 := by
  intro e0
  fin_cases e0
  · exact complete_287_0
  · exact complete_287_1
  · exact complete_287_2
  · exact complete_287_3
  · exact complete_287_4
#print axioms complete_case287
end Erdos184Work.PureSixLocalFilter1
