import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_383_0 : CompleteAt 383 0 := by decide +kernel
lemma complete_383_1 : CompleteAt 383 1 := by decide +kernel
lemma complete_383_2 : CompleteAt 383 2 := by decide +kernel
lemma complete_383_3 : CompleteAt 383 3 := by decide +kernel
lemma complete_383_4 : CompleteAt 383 4 := by decide +kernel
lemma complete_case383 : ∀ e0, CompleteAt 383 e0 := by
  intro e0
  fin_cases e0
  · exact complete_383_0
  · exact complete_383_1
  · exact complete_383_2
  · exact complete_383_3
  · exact complete_383_4
#print axioms complete_case383
end Erdos184Work.PureSixLocalFilter1
