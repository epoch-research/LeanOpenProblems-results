import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_13_0 : CompleteAt 13 0 := by decide +kernel
lemma complete_13_1 : CompleteAt 13 1 := by decide +kernel
lemma complete_13_2 : CompleteAt 13 2 := by decide +kernel
lemma complete_13_3 : CompleteAt 13 3 := by decide +kernel
lemma complete_13_4 : CompleteAt 13 4 := by decide +kernel
lemma complete_13_5 : CompleteAt 13 5 := by decide +kernel
lemma complete_case13 : ∀ e0, CompleteAt 13 e0 := by
  intro e0
  fin_cases e0
  · exact complete_13_0
  · exact complete_13_1
  · exact complete_13_2
  · exact complete_13_3
  · exact complete_13_4
  · exact complete_13_5
#print axioms complete_case13
end Erdos184Work.PureSixLocalFilter4
