import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_317_0 : CompleteAt 317 0 := by decide +kernel
lemma complete_317_1 : CompleteAt 317 1 := by decide +kernel
lemma complete_317_2 : CompleteAt 317 2 := by decide +kernel
lemma complete_317_3 : CompleteAt 317 3 := by decide +kernel
lemma complete_317_4 : CompleteAt 317 4 := by decide +kernel
lemma complete_case317 : ∀ e0, CompleteAt 317 e0 := by
  intro e0
  fin_cases e0
  · exact complete_317_0
  · exact complete_317_1
  · exact complete_317_2
  · exact complete_317_3
  · exact complete_317_4
#print axioms complete_case317
end Erdos184Work.PureSixLocalFilter1
