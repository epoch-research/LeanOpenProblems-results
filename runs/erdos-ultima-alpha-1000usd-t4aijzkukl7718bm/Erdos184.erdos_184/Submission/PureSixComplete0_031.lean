import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_31_0 : CompleteAt 31 0 := by decide +kernel
lemma complete_31_1 : CompleteAt 31 1 := by decide +kernel
lemma complete_31_2 : CompleteAt 31 2 := by decide +kernel
lemma complete_31_3 : CompleteAt 31 3 := by decide +kernel
lemma complete_case31 : ∀ e0, CompleteAt 31 e0 := by
  intro e0
  fin_cases e0
  · exact complete_31_0
  · exact complete_31_1
  · exact complete_31_2
  · exact complete_31_3
#print axioms complete_case31
end Erdos184Work.PureSixLocalFilter0
