import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_2_0 : CompleteAt 2 0 := by decide +kernel
lemma complete_2_1 : CompleteAt 2 1 := by decide +kernel
lemma complete_2_2 : CompleteAt 2 2 := by decide +kernel
lemma complete_2_3 : CompleteAt 2 3 := by decide +kernel
lemma complete_2_4 : CompleteAt 2 4 := by decide +kernel
lemma complete_2_5 : CompleteAt 2 5 := by decide +kernel
lemma complete_case2 : ∀ e0, CompleteAt 2 e0 := by
  intro e0
  fin_cases e0
  · exact complete_2_0
  · exact complete_2_1
  · exact complete_2_2
  · exact complete_2_3
  · exact complete_2_4
  · exact complete_2_5
#print axioms complete_case2
end Erdos184Work.PureSixLocalFilter4
