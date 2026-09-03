import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_84_0 : CompleteAt 84 0 := by decide +kernel
lemma complete_84_1 : CompleteAt 84 1 := by decide +kernel
lemma complete_84_2 : CompleteAt 84 2 := by decide +kernel
lemma complete_84_3 : CompleteAt 84 3 := by decide +kernel
lemma complete_case84 : ∀ e0, CompleteAt 84 e0 := by
  intro e0
  fin_cases e0
  · exact complete_84_0
  · exact complete_84_1
  · exact complete_84_2
  · exact complete_84_3
#print axioms complete_case84
end Erdos184Work.PureSixLocalFilter0
