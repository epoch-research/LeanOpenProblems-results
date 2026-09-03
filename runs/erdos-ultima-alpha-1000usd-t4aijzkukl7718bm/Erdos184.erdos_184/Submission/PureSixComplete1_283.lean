import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_283_0 : CompleteAt 283 0 := by decide +kernel
lemma complete_283_1 : CompleteAt 283 1 := by decide +kernel
lemma complete_283_2 : CompleteAt 283 2 := by decide +kernel
lemma complete_283_3 : CompleteAt 283 3 := by decide +kernel
lemma complete_283_4 : CompleteAt 283 4 := by decide +kernel
lemma complete_case283 : ∀ e0, CompleteAt 283 e0 := by
  intro e0
  fin_cases e0
  · exact complete_283_0
  · exact complete_283_1
  · exact complete_283_2
  · exact complete_283_3
  · exact complete_283_4
#print axioms complete_case283
end Erdos184Work.PureSixLocalFilter1
