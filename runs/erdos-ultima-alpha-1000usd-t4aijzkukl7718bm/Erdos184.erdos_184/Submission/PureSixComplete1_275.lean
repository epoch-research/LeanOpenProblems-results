import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_275_0 : CompleteAt 275 0 := by decide +kernel
lemma complete_275_1 : CompleteAt 275 1 := by decide +kernel
lemma complete_275_2 : CompleteAt 275 2 := by decide +kernel
lemma complete_275_3 : CompleteAt 275 3 := by decide +kernel
lemma complete_275_4 : CompleteAt 275 4 := by decide +kernel
lemma complete_case275 : ∀ e0, CompleteAt 275 e0 := by
  intro e0
  fin_cases e0
  · exact complete_275_0
  · exact complete_275_1
  · exact complete_275_2
  · exact complete_275_3
  · exact complete_275_4
#print axioms complete_case275
end Erdos184Work.PureSixLocalFilter1
