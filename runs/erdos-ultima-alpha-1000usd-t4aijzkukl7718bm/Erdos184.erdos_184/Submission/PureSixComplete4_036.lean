import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_36_0 : CompleteAt 36 0 := by decide +kernel
lemma complete_36_1 : CompleteAt 36 1 := by decide +kernel
lemma complete_36_2 : CompleteAt 36 2 := by decide +kernel
lemma complete_36_3 : CompleteAt 36 3 := by decide +kernel
lemma complete_36_4 : CompleteAt 36 4 := by decide +kernel
lemma complete_36_5 : CompleteAt 36 5 := by decide +kernel
lemma complete_case36 : ∀ e0, CompleteAt 36 e0 := by
  intro e0
  fin_cases e0
  · exact complete_36_0
  · exact complete_36_1
  · exact complete_36_2
  · exact complete_36_3
  · exact complete_36_4
  · exact complete_36_5
#print axioms complete_case36
end Erdos184Work.PureSixLocalFilter4
