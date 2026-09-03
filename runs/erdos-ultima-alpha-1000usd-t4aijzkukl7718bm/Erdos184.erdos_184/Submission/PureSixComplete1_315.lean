import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_315_0 : CompleteAt 315 0 := by decide +kernel
lemma complete_315_1 : CompleteAt 315 1 := by decide +kernel
lemma complete_315_2 : CompleteAt 315 2 := by decide +kernel
lemma complete_315_3 : CompleteAt 315 3 := by decide +kernel
lemma complete_315_4 : CompleteAt 315 4 := by decide +kernel
lemma complete_case315 : ∀ e0, CompleteAt 315 e0 := by
  intro e0
  fin_cases e0
  · exact complete_315_0
  · exact complete_315_1
  · exact complete_315_2
  · exact complete_315_3
  · exact complete_315_4
#print axioms complete_case315
end Erdos184Work.PureSixLocalFilter1
