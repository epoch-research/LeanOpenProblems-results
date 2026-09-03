import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_99_0 : CompleteAt 99 0 := by decide +kernel
lemma complete_99_1 : CompleteAt 99 1 := by decide +kernel
lemma complete_99_2 : CompleteAt 99 2 := by decide +kernel
lemma complete_99_3 : CompleteAt 99 3 := by decide +kernel
lemma complete_case99 : ∀ e0, CompleteAt 99 e0 := by
  intro e0
  fin_cases e0
  · exact complete_99_0
  · exact complete_99_1
  · exact complete_99_2
  · exact complete_99_3
#print axioms complete_case99
end Erdos184Work.PureSixLocalFilter0
