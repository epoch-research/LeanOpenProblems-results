import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_375_0 : CompleteAt 375 0 := by decide +kernel
lemma complete_375_1 : CompleteAt 375 1 := by decide +kernel
lemma complete_375_2 : CompleteAt 375 2 := by decide +kernel
lemma complete_375_3 : CompleteAt 375 3 := by decide +kernel
lemma complete_375_4 : CompleteAt 375 4 := by decide +kernel
lemma complete_case375 : ∀ e0, CompleteAt 375 e0 := by
  intro e0
  fin_cases e0
  · exact complete_375_0
  · exact complete_375_1
  · exact complete_375_2
  · exact complete_375_3
  · exact complete_375_4
#print axioms complete_case375
end Erdos184Work.PureSixLocalFilter1
