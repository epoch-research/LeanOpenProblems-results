import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_204_0 : CompleteAt 204 0 := by decide +kernel
lemma complete_204_1 : CompleteAt 204 1 := by decide +kernel
lemma complete_204_2 : CompleteAt 204 2 := by decide +kernel
lemma complete_204_3 : CompleteAt 204 3 := by decide +kernel
lemma complete_204_4 : CompleteAt 204 4 := by decide +kernel
lemma complete_case204 : ∀ e0, CompleteAt 204 e0 := by
  intro e0
  fin_cases e0
  · exact complete_204_0
  · exact complete_204_1
  · exact complete_204_2
  · exact complete_204_3
  · exact complete_204_4
#print axioms complete_case204
end Erdos184Work.PureSixLocalFilter1
