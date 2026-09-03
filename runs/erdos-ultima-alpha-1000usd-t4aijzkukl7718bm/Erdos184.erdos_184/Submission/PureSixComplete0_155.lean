import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_155_0 : CompleteAt 155 0 := by decide +kernel
lemma complete_155_1 : CompleteAt 155 1 := by decide +kernel
lemma complete_155_2 : CompleteAt 155 2 := by decide +kernel
lemma complete_155_3 : CompleteAt 155 3 := by decide +kernel
lemma complete_case155 : ∀ e0, CompleteAt 155 e0 := by
  intro e0
  fin_cases e0
  · exact complete_155_0
  · exact complete_155_1
  · exact complete_155_2
  · exact complete_155_3
#print axioms complete_case155
end Erdos184Work.PureSixLocalFilter0
