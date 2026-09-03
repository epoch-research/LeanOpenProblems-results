import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_27_0 : CompleteAt 27 0 := by decide +kernel
lemma complete_27_1 : CompleteAt 27 1 := by decide +kernel
lemma complete_27_2 : CompleteAt 27 2 := by decide +kernel
lemma complete_27_3 : CompleteAt 27 3 := by decide +kernel
lemma complete_case27 : ∀ e0, CompleteAt 27 e0 := by
  intro e0
  fin_cases e0
  · exact complete_27_0
  · exact complete_27_1
  · exact complete_27_2
  · exact complete_27_3
#print axioms complete_case27
end Erdos184Work.PureSixLocalFilter0
