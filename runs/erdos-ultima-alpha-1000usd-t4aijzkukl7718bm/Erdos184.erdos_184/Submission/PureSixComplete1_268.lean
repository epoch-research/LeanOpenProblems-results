import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_268_0 : CompleteAt 268 0 := by decide +kernel
lemma complete_268_1 : CompleteAt 268 1 := by decide +kernel
lemma complete_268_2 : CompleteAt 268 2 := by decide +kernel
lemma complete_268_3 : CompleteAt 268 3 := by decide +kernel
lemma complete_268_4 : CompleteAt 268 4 := by decide +kernel
lemma complete_case268 : ∀ e0, CompleteAt 268 e0 := by
  intro e0
  fin_cases e0
  · exact complete_268_0
  · exact complete_268_1
  · exact complete_268_2
  · exact complete_268_3
  · exact complete_268_4
#print axioms complete_case268
end Erdos184Work.PureSixLocalFilter1
