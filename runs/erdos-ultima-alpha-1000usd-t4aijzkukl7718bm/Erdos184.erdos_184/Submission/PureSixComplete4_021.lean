import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_21_0 : CompleteAt 21 0 := by decide +kernel
lemma complete_21_1 : CompleteAt 21 1 := by decide +kernel
lemma complete_21_2 : CompleteAt 21 2 := by decide +kernel
lemma complete_21_3 : CompleteAt 21 3 := by decide +kernel
lemma complete_21_4 : CompleteAt 21 4 := by decide +kernel
lemma complete_21_5 : CompleteAt 21 5 := by decide +kernel
lemma complete_case21 : ∀ e0, CompleteAt 21 e0 := by
  intro e0
  fin_cases e0
  · exact complete_21_0
  · exact complete_21_1
  · exact complete_21_2
  · exact complete_21_3
  · exact complete_21_4
  · exact complete_21_5
#print axioms complete_case21
end Erdos184Work.PureSixLocalFilter4
