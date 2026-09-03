import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_35_0 : CompleteAt 35 0 := by decide +kernel
lemma complete_35_1 : CompleteAt 35 1 := by decide +kernel
lemma complete_35_2 : CompleteAt 35 2 := by decide +kernel
lemma complete_35_3 : CompleteAt 35 3 := by decide +kernel
lemma complete_case35 : ∀ e0, CompleteAt 35 e0 := by
  intro e0
  fin_cases e0
  · exact complete_35_0
  · exact complete_35_1
  · exact complete_35_2
  · exact complete_35_3
#print axioms complete_case35
end Erdos184Work.PureSixLocalFilter0
