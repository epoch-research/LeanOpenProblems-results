import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_207_0 : CompleteAt 207 0 := by decide +kernel
lemma complete_207_1 : CompleteAt 207 1 := by decide +kernel
lemma complete_207_2 : CompleteAt 207 2 := by decide +kernel
lemma complete_207_3 : CompleteAt 207 3 := by decide +kernel
lemma complete_207_4 : CompleteAt 207 4 := by decide +kernel
lemma complete_case207 : ∀ e0, CompleteAt 207 e0 := by
  intro e0
  fin_cases e0
  · exact complete_207_0
  · exact complete_207_1
  · exact complete_207_2
  · exact complete_207_3
  · exact complete_207_4
#print axioms complete_case207
end Erdos184Work.PureSixLocalFilter1
