import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_178_0 : CompleteAt 178 0 := by decide +kernel
lemma complete_178_1 : CompleteAt 178 1 := by decide +kernel
lemma complete_178_2 : CompleteAt 178 2 := by decide +kernel
lemma complete_178_3 : CompleteAt 178 3 := by decide +kernel
lemma complete_178_4 : CompleteAt 178 4 := by decide +kernel
lemma complete_case178 : ∀ e0, CompleteAt 178 e0 := by
  intro e0
  fin_cases e0
  · exact complete_178_0
  · exact complete_178_1
  · exact complete_178_2
  · exact complete_178_3
  · exact complete_178_4
#print axioms complete_case178
end Erdos184Work.PureSixLocalFilter1
