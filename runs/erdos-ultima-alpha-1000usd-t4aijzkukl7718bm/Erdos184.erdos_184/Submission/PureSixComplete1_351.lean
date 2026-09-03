import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_351_0 : CompleteAt 351 0 := by decide +kernel
lemma complete_351_1 : CompleteAt 351 1 := by decide +kernel
lemma complete_351_2 : CompleteAt 351 2 := by decide +kernel
lemma complete_351_3 : CompleteAt 351 3 := by decide +kernel
lemma complete_351_4 : CompleteAt 351 4 := by decide +kernel
lemma complete_case351 : ∀ e0, CompleteAt 351 e0 := by
  intro e0
  fin_cases e0
  · exact complete_351_0
  · exact complete_351_1
  · exact complete_351_2
  · exact complete_351_3
  · exact complete_351_4
#print axioms complete_case351
end Erdos184Work.PureSixLocalFilter1
