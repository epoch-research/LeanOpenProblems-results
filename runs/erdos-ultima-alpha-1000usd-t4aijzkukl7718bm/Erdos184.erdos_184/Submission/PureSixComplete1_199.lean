import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_199_0 : CompleteAt 199 0 := by decide +kernel
lemma complete_199_1 : CompleteAt 199 1 := by decide +kernel
lemma complete_199_2 : CompleteAt 199 2 := by decide +kernel
lemma complete_199_3 : CompleteAt 199 3 := by decide +kernel
lemma complete_199_4 : CompleteAt 199 4 := by decide +kernel
lemma complete_case199 : ∀ e0, CompleteAt 199 e0 := by
  intro e0
  fin_cases e0
  · exact complete_199_0
  · exact complete_199_1
  · exact complete_199_2
  · exact complete_199_3
  · exact complete_199_4
#print axioms complete_case199
end Erdos184Work.PureSixLocalFilter1
