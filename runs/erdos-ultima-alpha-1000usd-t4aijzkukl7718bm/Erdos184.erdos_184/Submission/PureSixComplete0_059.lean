import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_59_0 : CompleteAt 59 0 := by decide +kernel
lemma complete_59_1 : CompleteAt 59 1 := by decide +kernel
lemma complete_59_2 : CompleteAt 59 2 := by decide +kernel
lemma complete_59_3 : CompleteAt 59 3 := by decide +kernel
lemma complete_case59 : ∀ e0, CompleteAt 59 e0 := by
  intro e0
  fin_cases e0
  · exact complete_59_0
  · exact complete_59_1
  · exact complete_59_2
  · exact complete_59_3
#print axioms complete_case59
end Erdos184Work.PureSixLocalFilter0
