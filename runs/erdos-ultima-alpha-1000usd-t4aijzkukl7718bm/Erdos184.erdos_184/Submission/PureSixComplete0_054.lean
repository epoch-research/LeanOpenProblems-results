import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_54_0 : CompleteAt 54 0 := by decide +kernel
lemma complete_54_1 : CompleteAt 54 1 := by decide +kernel
lemma complete_54_2 : CompleteAt 54 2 := by decide +kernel
lemma complete_54_3 : CompleteAt 54 3 := by decide +kernel
lemma complete_case54 : ∀ e0, CompleteAt 54 e0 := by
  intro e0
  fin_cases e0
  · exact complete_54_0
  · exact complete_54_1
  · exact complete_54_2
  · exact complete_54_3
#print axioms complete_case54
end Erdos184Work.PureSixLocalFilter0
