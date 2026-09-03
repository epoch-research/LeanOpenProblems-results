import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_231_0 : CompleteAt 231 0 := by decide +kernel
lemma complete_231_1 : CompleteAt 231 1 := by decide +kernel
lemma complete_231_2 : CompleteAt 231 2 := by decide +kernel
lemma complete_231_3 : CompleteAt 231 3 := by decide +kernel
lemma complete_231_4 : CompleteAt 231 4 := by decide +kernel
lemma complete_case231 : ∀ e0, CompleteAt 231 e0 := by
  intro e0
  fin_cases e0
  · exact complete_231_0
  · exact complete_231_1
  · exact complete_231_2
  · exact complete_231_3
  · exact complete_231_4
#print axioms complete_case231
end Erdos184Work.PureSixLocalFilter1
