import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_122_0 : CompleteAt 122 0 := by decide +kernel
lemma complete_122_1 : CompleteAt 122 1 := by decide +kernel
lemma complete_122_2 : CompleteAt 122 2 := by decide +kernel
lemma complete_122_3 : CompleteAt 122 3 := by decide +kernel
lemma complete_case122 : ∀ e0, CompleteAt 122 e0 := by
  intro e0
  fin_cases e0
  · exact complete_122_0
  · exact complete_122_1
  · exact complete_122_2
  · exact complete_122_3
#print axioms complete_case122
end Erdos184Work.PureSixLocalFilter0
