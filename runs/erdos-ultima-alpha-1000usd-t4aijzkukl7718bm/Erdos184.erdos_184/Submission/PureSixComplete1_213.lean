import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_213_0 : CompleteAt 213 0 := by decide +kernel
lemma complete_213_1 : CompleteAt 213 1 := by decide +kernel
lemma complete_213_2 : CompleteAt 213 2 := by decide +kernel
lemma complete_213_3 : CompleteAt 213 3 := by decide +kernel
lemma complete_213_4 : CompleteAt 213 4 := by decide +kernel
lemma complete_case213 : ∀ e0, CompleteAt 213 e0 := by
  intro e0
  fin_cases e0
  · exact complete_213_0
  · exact complete_213_1
  · exact complete_213_2
  · exact complete_213_3
  · exact complete_213_4
#print axioms complete_case213
end Erdos184Work.PureSixLocalFilter1
