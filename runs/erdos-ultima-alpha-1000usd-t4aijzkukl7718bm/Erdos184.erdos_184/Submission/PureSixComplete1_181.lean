import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_181_0 : CompleteAt 181 0 := by decide +kernel
lemma complete_181_1 : CompleteAt 181 1 := by decide +kernel
lemma complete_181_2 : CompleteAt 181 2 := by decide +kernel
lemma complete_181_3 : CompleteAt 181 3 := by decide +kernel
lemma complete_181_4 : CompleteAt 181 4 := by decide +kernel
lemma complete_case181 : ∀ e0, CompleteAt 181 e0 := by
  intro e0
  fin_cases e0
  · exact complete_181_0
  · exact complete_181_1
  · exact complete_181_2
  · exact complete_181_3
  · exact complete_181_4
#print axioms complete_case181
end Erdos184Work.PureSixLocalFilter1
