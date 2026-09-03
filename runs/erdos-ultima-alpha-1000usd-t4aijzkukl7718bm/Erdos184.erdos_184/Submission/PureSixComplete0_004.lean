import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_4_0 : CompleteAt 4 0 := by decide +kernel
lemma complete_4_1 : CompleteAt 4 1 := by decide +kernel
lemma complete_4_2 : CompleteAt 4 2 := by decide +kernel
lemma complete_4_3 : CompleteAt 4 3 := by decide +kernel
lemma complete_case4 : ∀ e0, CompleteAt 4 e0 := by
  intro e0
  fin_cases e0
  · exact complete_4_0
  · exact complete_4_1
  · exact complete_4_2
  · exact complete_4_3
#print axioms complete_case4
end Erdos184Work.PureSixLocalFilter0
