import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_341_0 : CompleteAt 341 0 := by decide +kernel
lemma complete_341_1 : CompleteAt 341 1 := by decide +kernel
lemma complete_341_2 : CompleteAt 341 2 := by decide +kernel
lemma complete_341_3 : CompleteAt 341 3 := by decide +kernel
lemma complete_341_4 : CompleteAt 341 4 := by decide +kernel
lemma complete_case341 : ∀ e0, CompleteAt 341 e0 := by
  intro e0
  fin_cases e0
  · exact complete_341_0
  · exact complete_341_1
  · exact complete_341_2
  · exact complete_341_3
  · exact complete_341_4
#print axioms complete_case341
end Erdos184Work.PureSixLocalFilter1
