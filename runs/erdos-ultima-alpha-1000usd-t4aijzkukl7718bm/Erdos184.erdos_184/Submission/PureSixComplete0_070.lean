import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_70_0 : CompleteAt 70 0 := by decide +kernel
lemma complete_70_1 : CompleteAt 70 1 := by decide +kernel
lemma complete_70_2 : CompleteAt 70 2 := by decide +kernel
lemma complete_70_3 : CompleteAt 70 3 := by decide +kernel
lemma complete_case70 : ∀ e0, CompleteAt 70 e0 := by
  intro e0
  fin_cases e0
  · exact complete_70_0
  · exact complete_70_1
  · exact complete_70_2
  · exact complete_70_3
#print axioms complete_case70
end Erdos184Work.PureSixLocalFilter0
