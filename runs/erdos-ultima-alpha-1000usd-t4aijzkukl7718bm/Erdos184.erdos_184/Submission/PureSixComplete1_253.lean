import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_253_0 : CompleteAt 253 0 := by decide +kernel
lemma complete_253_1 : CompleteAt 253 1 := by decide +kernel
lemma complete_253_2 : CompleteAt 253 2 := by decide +kernel
lemma complete_253_3 : CompleteAt 253 3 := by decide +kernel
lemma complete_253_4 : CompleteAt 253 4 := by decide +kernel
lemma complete_case253 : ∀ e0, CompleteAt 253 e0 := by
  intro e0
  fin_cases e0
  · exact complete_253_0
  · exact complete_253_1
  · exact complete_253_2
  · exact complete_253_3
  · exact complete_253_4
#print axioms complete_case253
end Erdos184Work.PureSixLocalFilter1
