import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_25_0 : CompleteAt 25 0 := by decide +kernel
lemma complete_25_1 : CompleteAt 25 1 := by decide +kernel
lemma complete_25_2 : CompleteAt 25 2 := by decide +kernel
lemma complete_25_3 : CompleteAt 25 3 := by decide +kernel
lemma complete_case25 : ∀ e0, CompleteAt 25 e0 := by
  intro e0
  fin_cases e0
  · exact complete_25_0
  · exact complete_25_1
  · exact complete_25_2
  · exact complete_25_3
#print axioms complete_case25
end Erdos184Work.PureSixLocalFilter0
