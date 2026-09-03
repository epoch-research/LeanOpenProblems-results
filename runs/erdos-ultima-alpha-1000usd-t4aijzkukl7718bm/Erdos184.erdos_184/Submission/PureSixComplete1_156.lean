import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_156_0 : CompleteAt 156 0 := by decide +kernel
lemma complete_156_1 : CompleteAt 156 1 := by decide +kernel
lemma complete_156_2 : CompleteAt 156 2 := by decide +kernel
lemma complete_156_3 : CompleteAt 156 3 := by decide +kernel
lemma complete_156_4 : CompleteAt 156 4 := by decide +kernel
lemma complete_case156 : ∀ e0, CompleteAt 156 e0 := by
  intro e0
  fin_cases e0
  · exact complete_156_0
  · exact complete_156_1
  · exact complete_156_2
  · exact complete_156_3
  · exact complete_156_4
#print axioms complete_case156
end Erdos184Work.PureSixLocalFilter1
