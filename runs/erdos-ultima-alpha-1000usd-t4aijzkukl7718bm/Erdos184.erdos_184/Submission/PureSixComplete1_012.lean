import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_12_0 : CompleteAt 12 0 := by decide +kernel
lemma complete_12_1 : CompleteAt 12 1 := by decide +kernel
lemma complete_12_2 : CompleteAt 12 2 := by decide +kernel
lemma complete_12_3 : CompleteAt 12 3 := by decide +kernel
lemma complete_12_4 : CompleteAt 12 4 := by decide +kernel
lemma complete_case12 : ∀ e0, CompleteAt 12 e0 := by
  intro e0
  fin_cases e0
  · exact complete_12_0
  · exact complete_12_1
  · exact complete_12_2
  · exact complete_12_3
  · exact complete_12_4
#print axioms complete_case12
end Erdos184Work.PureSixLocalFilter1
