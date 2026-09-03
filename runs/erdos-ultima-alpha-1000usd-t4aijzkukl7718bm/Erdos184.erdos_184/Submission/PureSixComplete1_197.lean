import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_197_0 : CompleteAt 197 0 := by decide +kernel
lemma complete_197_1 : CompleteAt 197 1 := by decide +kernel
lemma complete_197_2 : CompleteAt 197 2 := by decide +kernel
lemma complete_197_3 : CompleteAt 197 3 := by decide +kernel
lemma complete_197_4 : CompleteAt 197 4 := by decide +kernel
lemma complete_case197 : ∀ e0, CompleteAt 197 e0 := by
  intro e0
  fin_cases e0
  · exact complete_197_0
  · exact complete_197_1
  · exact complete_197_2
  · exact complete_197_3
  · exact complete_197_4
#print axioms complete_case197
end Erdos184Work.PureSixLocalFilter1
