import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_365_0 : CompleteAt 365 0 := by decide +kernel
lemma complete_365_1 : CompleteAt 365 1 := by decide +kernel
lemma complete_365_2 : CompleteAt 365 2 := by decide +kernel
lemma complete_365_3 : CompleteAt 365 3 := by decide +kernel
lemma complete_365_4 : CompleteAt 365 4 := by decide +kernel
lemma complete_case365 : ∀ e0, CompleteAt 365 e0 := by
  intro e0
  fin_cases e0
  · exact complete_365_0
  · exact complete_365_1
  · exact complete_365_2
  · exact complete_365_3
  · exact complete_365_4
#print axioms complete_case365
end Erdos184Work.PureSixLocalFilter1
