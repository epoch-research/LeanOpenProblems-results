import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_280_0 : CompleteAt 280 0 := by decide +kernel
lemma complete_280_1 : CompleteAt 280 1 := by decide +kernel
lemma complete_280_2 : CompleteAt 280 2 := by decide +kernel
lemma complete_280_3 : CompleteAt 280 3 := by decide +kernel
lemma complete_280_4 : CompleteAt 280 4 := by decide +kernel
lemma complete_case280 : ∀ e0, CompleteAt 280 e0 := by
  intro e0
  fin_cases e0
  · exact complete_280_0
  · exact complete_280_1
  · exact complete_280_2
  · exact complete_280_3
  · exact complete_280_4
#print axioms complete_case280
end Erdos184Work.PureSixLocalFilter1
