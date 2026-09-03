import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_11_0 : CompleteAt 11 0 := by decide +kernel
lemma complete_11_1 : CompleteAt 11 1 := by decide +kernel
lemma complete_11_2 : CompleteAt 11 2 := by decide +kernel
lemma complete_11_3 : CompleteAt 11 3 := by decide +kernel
lemma complete_case11 : ∀ e0, CompleteAt 11 e0 := by
  intro e0
  fin_cases e0
  · exact complete_11_0
  · exact complete_11_1
  · exact complete_11_2
  · exact complete_11_3
#print axioms complete_case11
end Erdos184Work.PureSixLocalFilter0
