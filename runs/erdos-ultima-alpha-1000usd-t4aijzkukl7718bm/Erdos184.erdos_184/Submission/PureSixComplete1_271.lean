import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_271_0 : CompleteAt 271 0 := by decide +kernel
lemma complete_271_1 : CompleteAt 271 1 := by decide +kernel
lemma complete_271_2 : CompleteAt 271 2 := by decide +kernel
lemma complete_271_3 : CompleteAt 271 3 := by decide +kernel
lemma complete_271_4 : CompleteAt 271 4 := by decide +kernel
lemma complete_case271 : ∀ e0, CompleteAt 271 e0 := by
  intro e0
  fin_cases e0
  · exact complete_271_0
  · exact complete_271_1
  · exact complete_271_2
  · exact complete_271_3
  · exact complete_271_4
#print axioms complete_case271
end Erdos184Work.PureSixLocalFilter1
