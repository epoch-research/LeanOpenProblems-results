import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_245_0 : CompleteAt 245 0 := by decide +kernel
lemma complete_245_1 : CompleteAt 245 1 := by decide +kernel
lemma complete_245_2 : CompleteAt 245 2 := by decide +kernel
lemma complete_245_3 : CompleteAt 245 3 := by decide +kernel
lemma complete_245_4 : CompleteAt 245 4 := by decide +kernel
lemma complete_case245 : ∀ e0, CompleteAt 245 e0 := by
  intro e0
  fin_cases e0
  · exact complete_245_0
  · exact complete_245_1
  · exact complete_245_2
  · exact complete_245_3
  · exact complete_245_4
#print axioms complete_case245
end Erdos184Work.PureSixLocalFilter1
