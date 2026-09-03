import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_32_0 : CompleteAt 32 0 := by decide +kernel
lemma complete_32_1 : CompleteAt 32 1 := by decide +kernel
lemma complete_32_2 : CompleteAt 32 2 := by decide +kernel
lemma complete_32_3 : CompleteAt 32 3 := by decide +kernel
lemma complete_case32 : ∀ e0, CompleteAt 32 e0 := by
  intro e0
  fin_cases e0
  · exact complete_32_0
  · exact complete_32_1
  · exact complete_32_2
  · exact complete_32_3
#print axioms complete_case32
end Erdos184Work.PureSixLocalFilter0
