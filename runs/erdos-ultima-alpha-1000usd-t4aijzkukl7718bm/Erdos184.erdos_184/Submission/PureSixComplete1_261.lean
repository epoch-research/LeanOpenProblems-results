import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_261_0 : CompleteAt 261 0 := by decide +kernel
lemma complete_261_1 : CompleteAt 261 1 := by decide +kernel
lemma complete_261_2 : CompleteAt 261 2 := by decide +kernel
lemma complete_261_3 : CompleteAt 261 3 := by decide +kernel
lemma complete_261_4 : CompleteAt 261 4 := by decide +kernel
lemma complete_case261 : ∀ e0, CompleteAt 261 e0 := by
  intro e0
  fin_cases e0
  · exact complete_261_0
  · exact complete_261_1
  · exact complete_261_2
  · exact complete_261_3
  · exact complete_261_4
#print axioms complete_case261
end Erdos184Work.PureSixLocalFilter1
