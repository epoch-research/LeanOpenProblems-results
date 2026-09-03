import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_101_0 : CompleteAt 101 0 := by decide +kernel
lemma complete_101_1 : CompleteAt 101 1 := by decide +kernel
lemma complete_101_2 : CompleteAt 101 2 := by decide +kernel
lemma complete_101_3 : CompleteAt 101 3 := by decide +kernel
lemma complete_case101 : ∀ e0, CompleteAt 101 e0 := by
  intro e0
  fin_cases e0
  · exact complete_101_0
  · exact complete_101_1
  · exact complete_101_2
  · exact complete_101_3
#print axioms complete_case101
end Erdos184Work.PureSixLocalFilter0
