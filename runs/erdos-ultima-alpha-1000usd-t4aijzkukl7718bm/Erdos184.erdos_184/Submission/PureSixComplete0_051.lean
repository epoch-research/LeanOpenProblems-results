import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_51_0 : CompleteAt 51 0 := by decide +kernel
lemma complete_51_1 : CompleteAt 51 1 := by decide +kernel
lemma complete_51_2 : CompleteAt 51 2 := by decide +kernel
lemma complete_51_3 : CompleteAt 51 3 := by decide +kernel
lemma complete_case51 : ∀ e0, CompleteAt 51 e0 := by
  intro e0
  fin_cases e0
  · exact complete_51_0
  · exact complete_51_1
  · exact complete_51_2
  · exact complete_51_3
#print axioms complete_case51
end Erdos184Work.PureSixLocalFilter0
