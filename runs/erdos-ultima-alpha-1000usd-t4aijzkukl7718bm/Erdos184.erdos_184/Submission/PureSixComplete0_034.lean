import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_34_0 : CompleteAt 34 0 := by decide +kernel
lemma complete_34_1 : CompleteAt 34 1 := by decide +kernel
lemma complete_34_2 : CompleteAt 34 2 := by decide +kernel
lemma complete_34_3 : CompleteAt 34 3 := by decide +kernel
lemma complete_case34 : ∀ e0, CompleteAt 34 e0 := by
  intro e0
  fin_cases e0
  · exact complete_34_0
  · exact complete_34_1
  · exact complete_34_2
  · exact complete_34_3
#print axioms complete_case34
end Erdos184Work.PureSixLocalFilter0
