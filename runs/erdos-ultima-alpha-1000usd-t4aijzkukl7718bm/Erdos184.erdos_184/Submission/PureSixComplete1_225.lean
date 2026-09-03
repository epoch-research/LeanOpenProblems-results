import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_225_0 : CompleteAt 225 0 := by decide +kernel
lemma complete_225_1 : CompleteAt 225 1 := by decide +kernel
lemma complete_225_2 : CompleteAt 225 2 := by decide +kernel
lemma complete_225_3 : CompleteAt 225 3 := by decide +kernel
lemma complete_225_4 : CompleteAt 225 4 := by decide +kernel
lemma complete_case225 : ∀ e0, CompleteAt 225 e0 := by
  intro e0
  fin_cases e0
  · exact complete_225_0
  · exact complete_225_1
  · exact complete_225_2
  · exact complete_225_3
  · exact complete_225_4
#print axioms complete_case225
end Erdos184Work.PureSixLocalFilter1
