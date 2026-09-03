import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_22_0 : CompleteAt 22 0 := by decide +kernel
lemma complete_22_1 : CompleteAt 22 1 := by decide +kernel
lemma complete_22_2 : CompleteAt 22 2 := by decide +kernel
lemma complete_22_3 : CompleteAt 22 3 := by decide +kernel
lemma complete_22_4 : CompleteAt 22 4 := by decide +kernel
lemma complete_22_5 : CompleteAt 22 5 := by decide +kernel
lemma complete_case22 : ∀ e0, CompleteAt 22 e0 := by
  intro e0
  fin_cases e0
  · exact complete_22_0
  · exact complete_22_1
  · exact complete_22_2
  · exact complete_22_3
  · exact complete_22_4
  · exact complete_22_5
#print axioms complete_case22
end Erdos184Work.PureSixLocalFilter4
