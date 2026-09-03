import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_79_0 : CompleteAt 79 0 := by decide +kernel
lemma complete_79_1 : CompleteAt 79 1 := by decide +kernel
lemma complete_79_2 : CompleteAt 79 2 := by decide +kernel
lemma complete_79_3 : CompleteAt 79 3 := by decide +kernel
lemma complete_case79 : ∀ e0, CompleteAt 79 e0 := by
  intro e0
  fin_cases e0
  · exact complete_79_0
  · exact complete_79_1
  · exact complete_79_2
  · exact complete_79_3
#print axioms complete_case79
end Erdos184Work.PureSixLocalFilter0
