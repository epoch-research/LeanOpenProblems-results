import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_26_0 : CompleteAt 26 0 := by decide +kernel
lemma complete_26_1 : CompleteAt 26 1 := by decide +kernel
lemma complete_26_2 : CompleteAt 26 2 := by decide +kernel
lemma complete_26_3 : CompleteAt 26 3 := by decide +kernel
lemma complete_case26 : ∀ e0, CompleteAt 26 e0 := by
  intro e0
  fin_cases e0
  · exact complete_26_0
  · exact complete_26_1
  · exact complete_26_2
  · exact complete_26_3
#print axioms complete_case26
end Erdos184Work.PureSixLocalFilter0
