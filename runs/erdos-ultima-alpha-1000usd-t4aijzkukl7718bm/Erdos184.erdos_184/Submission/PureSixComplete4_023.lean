import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_23_0 : CompleteAt 23 0 := by decide +kernel
lemma complete_23_1 : CompleteAt 23 1 := by decide +kernel
lemma complete_23_2 : CompleteAt 23 2 := by decide +kernel
lemma complete_23_3 : CompleteAt 23 3 := by decide +kernel
lemma complete_23_4 : CompleteAt 23 4 := by decide +kernel
lemma complete_23_5 : CompleteAt 23 5 := by decide +kernel
lemma complete_case23 : ∀ e0, CompleteAt 23 e0 := by
  intro e0
  fin_cases e0
  · exact complete_23_0
  · exact complete_23_1
  · exact complete_23_2
  · exact complete_23_3
  · exact complete_23_4
  · exact complete_23_5
#print axioms complete_case23
end Erdos184Work.PureSixLocalFilter4
