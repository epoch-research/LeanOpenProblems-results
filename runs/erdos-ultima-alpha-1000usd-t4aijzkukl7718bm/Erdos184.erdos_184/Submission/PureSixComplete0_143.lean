import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_143_0 : CompleteAt 143 0 := by decide +kernel
lemma complete_143_1 : CompleteAt 143 1 := by decide +kernel
lemma complete_143_2 : CompleteAt 143 2 := by decide +kernel
lemma complete_143_3 : CompleteAt 143 3 := by decide +kernel
lemma complete_case143 : ∀ e0, CompleteAt 143 e0 := by
  intro e0
  fin_cases e0
  · exact complete_143_0
  · exact complete_143_1
  · exact complete_143_2
  · exact complete_143_3
#print axioms complete_case143
end Erdos184Work.PureSixLocalFilter0
