import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_57_0 : CompleteAt 57 0 := by decide +kernel
lemma complete_57_1 : CompleteAt 57 1 := by decide +kernel
lemma complete_57_2 : CompleteAt 57 2 := by decide +kernel
lemma complete_57_3 : CompleteAt 57 3 := by decide +kernel
lemma complete_case57 : ∀ e0, CompleteAt 57 e0 := by
  intro e0
  fin_cases e0
  · exact complete_57_0
  · exact complete_57_1
  · exact complete_57_2
  · exact complete_57_3
#print axioms complete_case57
end Erdos184Work.PureSixLocalFilter0
