import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_28_0 : CompleteAt 28 0 := by decide +kernel
lemma complete_28_1 : CompleteAt 28 1 := by decide +kernel
lemma complete_28_2 : CompleteAt 28 2 := by decide +kernel
lemma complete_28_3 : CompleteAt 28 3 := by decide +kernel
lemma complete_case28 : ∀ e0, CompleteAt 28 e0 := by
  intro e0
  fin_cases e0
  · exact complete_28_0
  · exact complete_28_1
  · exact complete_28_2
  · exact complete_28_3
#print axioms complete_case28
end Erdos184Work.PureSixLocalFilter0
