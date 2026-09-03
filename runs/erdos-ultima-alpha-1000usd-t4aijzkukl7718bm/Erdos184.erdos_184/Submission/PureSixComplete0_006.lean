import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_6_0 : CompleteAt 6 0 := by decide +kernel
lemma complete_6_1 : CompleteAt 6 1 := by decide +kernel
lemma complete_6_2 : CompleteAt 6 2 := by decide +kernel
lemma complete_6_3 : CompleteAt 6 3 := by decide +kernel
lemma complete_case6 : ∀ e0, CompleteAt 6 e0 := by
  intro e0
  fin_cases e0
  · exact complete_6_0
  · exact complete_6_1
  · exact complete_6_2
  · exact complete_6_3
#print axioms complete_case6
end Erdos184Work.PureSixLocalFilter0
