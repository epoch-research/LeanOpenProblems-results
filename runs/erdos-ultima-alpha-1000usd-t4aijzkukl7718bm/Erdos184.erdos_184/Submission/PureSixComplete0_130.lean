import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_130_0 : CompleteAt 130 0 := by decide +kernel
lemma complete_130_1 : CompleteAt 130 1 := by decide +kernel
lemma complete_130_2 : CompleteAt 130 2 := by decide +kernel
lemma complete_130_3 : CompleteAt 130 3 := by decide +kernel
lemma complete_case130 : ∀ e0, CompleteAt 130 e0 := by
  intro e0
  fin_cases e0
  · exact complete_130_0
  · exact complete_130_1
  · exact complete_130_2
  · exact complete_130_3
#print axioms complete_case130
end Erdos184Work.PureSixLocalFilter0
