import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_188_0 : CompleteAt 188 0 := by decide +kernel
lemma complete_188_1 : CompleteAt 188 1 := by decide +kernel
lemma complete_188_2 : CompleteAt 188 2 := by decide +kernel
lemma complete_188_3 : CompleteAt 188 3 := by decide +kernel
lemma complete_188_4 : CompleteAt 188 4 := by decide +kernel
lemma complete_case188 : ∀ e0, CompleteAt 188 e0 := by
  intro e0
  fin_cases e0
  · exact complete_188_0
  · exact complete_188_1
  · exact complete_188_2
  · exact complete_188_3
  · exact complete_188_4
#print axioms complete_case188
end Erdos184Work.PureSixLocalFilter1
