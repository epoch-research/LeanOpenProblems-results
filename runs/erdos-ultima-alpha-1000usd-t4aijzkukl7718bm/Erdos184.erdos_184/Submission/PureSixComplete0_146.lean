import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_146_0 : CompleteAt 146 0 := by decide +kernel
lemma complete_146_1 : CompleteAt 146 1 := by decide +kernel
lemma complete_146_2 : CompleteAt 146 2 := by decide +kernel
lemma complete_146_3 : CompleteAt 146 3 := by decide +kernel
lemma complete_case146 : ∀ e0, CompleteAt 146 e0 := by
  intro e0
  fin_cases e0
  · exact complete_146_0
  · exact complete_146_1
  · exact complete_146_2
  · exact complete_146_3
#print axioms complete_case146
end Erdos184Work.PureSixLocalFilter0
