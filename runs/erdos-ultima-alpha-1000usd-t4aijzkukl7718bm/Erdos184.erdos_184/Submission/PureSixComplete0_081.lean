import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_81_0 : CompleteAt 81 0 := by decide +kernel
lemma complete_81_1 : CompleteAt 81 1 := by decide +kernel
lemma complete_81_2 : CompleteAt 81 2 := by decide +kernel
lemma complete_81_3 : CompleteAt 81 3 := by decide +kernel
lemma complete_case81 : ∀ e0, CompleteAt 81 e0 := by
  intro e0
  fin_cases e0
  · exact complete_81_0
  · exact complete_81_1
  · exact complete_81_2
  · exact complete_81_3
#print axioms complete_case81
end Erdos184Work.PureSixLocalFilter0
