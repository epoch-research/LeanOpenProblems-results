import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_368_0 : CompleteAt 368 0 := by decide +kernel
lemma complete_368_1 : CompleteAt 368 1 := by decide +kernel
lemma complete_368_2 : CompleteAt 368 2 := by decide +kernel
lemma complete_368_3 : CompleteAt 368 3 := by decide +kernel
lemma complete_368_4 : CompleteAt 368 4 := by decide +kernel
lemma complete_case368 : ∀ e0, CompleteAt 368 e0 := by
  intro e0
  fin_cases e0
  · exact complete_368_0
  · exact complete_368_1
  · exact complete_368_2
  · exact complete_368_3
  · exact complete_368_4
#print axioms complete_case368
end Erdos184Work.PureSixLocalFilter1
