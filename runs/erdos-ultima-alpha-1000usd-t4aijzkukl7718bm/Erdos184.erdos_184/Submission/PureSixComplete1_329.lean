import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_329_0 : CompleteAt 329 0 := by decide +kernel
lemma complete_329_1 : CompleteAt 329 1 := by decide +kernel
lemma complete_329_2 : CompleteAt 329 2 := by decide +kernel
lemma complete_329_3 : CompleteAt 329 3 := by decide +kernel
lemma complete_329_4 : CompleteAt 329 4 := by decide +kernel
lemma complete_case329 : ∀ e0, CompleteAt 329 e0 := by
  intro e0
  fin_cases e0
  · exact complete_329_0
  · exact complete_329_1
  · exact complete_329_2
  · exact complete_329_3
  · exact complete_329_4
#print axioms complete_case329
end Erdos184Work.PureSixLocalFilter1
