import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_170_0 : CompleteAt 170 0 := by decide +kernel
lemma complete_170_1 : CompleteAt 170 1 := by decide +kernel
lemma complete_170_2 : CompleteAt 170 2 := by decide +kernel
lemma complete_170_3 : CompleteAt 170 3 := by decide +kernel
lemma complete_170_4 : CompleteAt 170 4 := by decide +kernel
lemma complete_case170 : ∀ e0, CompleteAt 170 e0 := by
  intro e0
  fin_cases e0
  · exact complete_170_0
  · exact complete_170_1
  · exact complete_170_2
  · exact complete_170_3
  · exact complete_170_4
#print axioms complete_case170
end Erdos184Work.PureSixLocalFilter1
