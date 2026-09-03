import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_23_0 : CompleteAt 23 0 := by decide +kernel
lemma complete_23_1 : CompleteAt 23 1 := by decide +kernel
lemma complete_23_2 : CompleteAt 23 2 := by decide +kernel
lemma complete_23_3 : CompleteAt 23 3 := by decide +kernel
lemma complete_case23 : ∀ e0, CompleteAt 23 e0 := by
  intro e0
  fin_cases e0
  · exact complete_23_0
  · exact complete_23_1
  · exact complete_23_2
  · exact complete_23_3
#print axioms complete_case23
end Erdos184Work.PureSixLocalFilter0
