import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_16_0 : CompleteAt 16 0 := by decide +kernel
lemma complete_16_1 : CompleteAt 16 1 := by decide +kernel
lemma complete_16_2 : CompleteAt 16 2 := by decide +kernel
lemma complete_16_3 : CompleteAt 16 3 := by decide +kernel
lemma complete_case16 : ∀ e0, CompleteAt 16 e0 := by
  intro e0
  fin_cases e0
  · exact complete_16_0
  · exact complete_16_1
  · exact complete_16_2
  · exact complete_16_3
#print axioms complete_case16
end Erdos184Work.PureSixLocalFilter0
