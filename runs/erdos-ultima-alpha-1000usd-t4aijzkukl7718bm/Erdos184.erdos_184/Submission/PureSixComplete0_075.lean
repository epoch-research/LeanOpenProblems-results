import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_75_0 : CompleteAt 75 0 := by decide +kernel
lemma complete_75_1 : CompleteAt 75 1 := by decide +kernel
lemma complete_75_2 : CompleteAt 75 2 := by decide +kernel
lemma complete_75_3 : CompleteAt 75 3 := by decide +kernel
lemma complete_case75 : ∀ e0, CompleteAt 75 e0 := by
  intro e0
  fin_cases e0
  · exact complete_75_0
  · exact complete_75_1
  · exact complete_75_2
  · exact complete_75_3
#print axioms complete_case75
end Erdos184Work.PureSixLocalFilter0
