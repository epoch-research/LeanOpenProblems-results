import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_138_0 : CompleteAt 138 0 := by decide +kernel
lemma complete_138_1 : CompleteAt 138 1 := by decide +kernel
lemma complete_138_2 : CompleteAt 138 2 := by decide +kernel
lemma complete_138_3 : CompleteAt 138 3 := by decide +kernel
lemma complete_case138 : ∀ e0, CompleteAt 138 e0 := by
  intro e0
  fin_cases e0
  · exact complete_138_0
  · exact complete_138_1
  · exact complete_138_2
  · exact complete_138_3
#print axioms complete_case138
end Erdos184Work.PureSixLocalFilter0
