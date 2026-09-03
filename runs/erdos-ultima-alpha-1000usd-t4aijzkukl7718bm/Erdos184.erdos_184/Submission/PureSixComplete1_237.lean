import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_237_0 : CompleteAt 237 0 := by decide +kernel
lemma complete_237_1 : CompleteAt 237 1 := by decide +kernel
lemma complete_237_2 : CompleteAt 237 2 := by decide +kernel
lemma complete_237_3 : CompleteAt 237 3 := by decide +kernel
lemma complete_237_4 : CompleteAt 237 4 := by decide +kernel
lemma complete_case237 : ∀ e0, CompleteAt 237 e0 := by
  intro e0
  fin_cases e0
  · exact complete_237_0
  · exact complete_237_1
  · exact complete_237_2
  · exact complete_237_3
  · exact complete_237_4
#print axioms complete_case237
end Erdos184Work.PureSixLocalFilter1
