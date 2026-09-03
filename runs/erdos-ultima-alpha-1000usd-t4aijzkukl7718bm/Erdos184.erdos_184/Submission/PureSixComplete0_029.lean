import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_29_0 : CompleteAt 29 0 := by decide +kernel
lemma complete_29_1 : CompleteAt 29 1 := by decide +kernel
lemma complete_29_2 : CompleteAt 29 2 := by decide +kernel
lemma complete_29_3 : CompleteAt 29 3 := by decide +kernel
lemma complete_case29 : ∀ e0, CompleteAt 29 e0 := by
  intro e0
  fin_cases e0
  · exact complete_29_0
  · exact complete_29_1
  · exact complete_29_2
  · exact complete_29_3
#print axioms complete_case29
end Erdos184Work.PureSixLocalFilter0
