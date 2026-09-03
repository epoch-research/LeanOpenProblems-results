import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_290_0 : CompleteAt 290 0 := by decide +kernel
lemma complete_290_1 : CompleteAt 290 1 := by decide +kernel
lemma complete_290_2 : CompleteAt 290 2 := by decide +kernel
lemma complete_290_3 : CompleteAt 290 3 := by decide +kernel
lemma complete_290_4 : CompleteAt 290 4 := by decide +kernel
lemma complete_case290 : ∀ e0, CompleteAt 290 e0 := by
  intro e0
  fin_cases e0
  · exact complete_290_0
  · exact complete_290_1
  · exact complete_290_2
  · exact complete_290_3
  · exact complete_290_4
#print axioms complete_case290
end Erdos184Work.PureSixLocalFilter1
