import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_377_0 : CompleteAt 377 0 := by decide +kernel
lemma complete_377_1 : CompleteAt 377 1 := by decide +kernel
lemma complete_377_2 : CompleteAt 377 2 := by decide +kernel
lemma complete_377_3 : CompleteAt 377 3 := by decide +kernel
lemma complete_377_4 : CompleteAt 377 4 := by decide +kernel
lemma complete_case377 : ∀ e0, CompleteAt 377 e0 := by
  intro e0
  fin_cases e0
  · exact complete_377_0
  · exact complete_377_1
  · exact complete_377_2
  · exact complete_377_3
  · exact complete_377_4
#print axioms complete_case377
end Erdos184Work.PureSixLocalFilter1
