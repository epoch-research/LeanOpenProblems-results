import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_196_0 : CompleteAt 196 0 := by decide +kernel
lemma complete_196_1 : CompleteAt 196 1 := by decide +kernel
lemma complete_196_2 : CompleteAt 196 2 := by decide +kernel
lemma complete_196_3 : CompleteAt 196 3 := by decide +kernel
lemma complete_196_4 : CompleteAt 196 4 := by decide +kernel
lemma complete_case196 : ∀ e0, CompleteAt 196 e0 := by
  intro e0
  fin_cases e0
  · exact complete_196_0
  · exact complete_196_1
  · exact complete_196_2
  · exact complete_196_3
  · exact complete_196_4
#print axioms complete_case196
end Erdos184Work.PureSixLocalFilter1
