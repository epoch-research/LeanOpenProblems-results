import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_292_0 : CompleteAt 292 0 := by decide +kernel
lemma complete_292_1 : CompleteAt 292 1 := by decide +kernel
lemma complete_292_2 : CompleteAt 292 2 := by decide +kernel
lemma complete_292_3 : CompleteAt 292 3 := by decide +kernel
lemma complete_292_4 : CompleteAt 292 4 := by decide +kernel
lemma complete_case292 : ∀ e0, CompleteAt 292 e0 := by
  intro e0
  fin_cases e0
  · exact complete_292_0
  · exact complete_292_1
  · exact complete_292_2
  · exact complete_292_3
  · exact complete_292_4
#print axioms complete_case292
end Erdos184Work.PureSixLocalFilter1
