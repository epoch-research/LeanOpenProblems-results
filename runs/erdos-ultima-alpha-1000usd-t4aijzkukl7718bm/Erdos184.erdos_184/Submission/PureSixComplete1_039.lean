import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_39_0 : CompleteAt 39 0 := by decide +kernel
lemma complete_39_1 : CompleteAt 39 1 := by decide +kernel
lemma complete_39_2 : CompleteAt 39 2 := by decide +kernel
lemma complete_39_3 : CompleteAt 39 3 := by decide +kernel
lemma complete_39_4 : CompleteAt 39 4 := by decide +kernel
lemma complete_case39 : ∀ e0, CompleteAt 39 e0 := by
  intro e0
  fin_cases e0
  · exact complete_39_0
  · exact complete_39_1
  · exact complete_39_2
  · exact complete_39_3
  · exact complete_39_4
#print axioms complete_case39
end Erdos184Work.PureSixLocalFilter1
