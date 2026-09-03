import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_115_0 : CompleteAt 115 0 := by decide +kernel
lemma complete_115_1 : CompleteAt 115 1 := by decide +kernel
lemma complete_115_2 : CompleteAt 115 2 := by decide +kernel
lemma complete_115_3 : CompleteAt 115 3 := by decide +kernel
lemma complete_115_4 : CompleteAt 115 4 := by decide +kernel
lemma complete_case115 : ∀ e0, CompleteAt 115 e0 := by
  intro e0
  fin_cases e0
  · exact complete_115_0
  · exact complete_115_1
  · exact complete_115_2
  · exact complete_115_3
  · exact complete_115_4
#print axioms complete_case115
end Erdos184Work.PureSixLocalFilter1
