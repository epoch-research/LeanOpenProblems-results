import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_9_0 : CompleteAt 9 0 := by decide +kernel
lemma complete_9_1 : CompleteAt 9 1 := by decide +kernel
lemma complete_9_2 : CompleteAt 9 2 := by decide +kernel
lemma complete_9_3 : CompleteAt 9 3 := by decide +kernel
lemma complete_9_4 : CompleteAt 9 4 := by decide +kernel
lemma complete_case9 : ∀ e0, CompleteAt 9 e0 := by
  intro e0
  fin_cases e0
  · exact complete_9_0
  · exact complete_9_1
  · exact complete_9_2
  · exact complete_9_3
  · exact complete_9_4
#print axioms complete_case9
end Erdos184Work.PureSixLocalFilter1
