import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_8_0 : CompleteAt 8 0 := by decide +kernel
lemma complete_8_1 : CompleteAt 8 1 := by decide +kernel
lemma complete_8_2 : CompleteAt 8 2 := by decide +kernel
lemma complete_8_3 : CompleteAt 8 3 := by decide +kernel
lemma complete_8_4 : CompleteAt 8 4 := by decide +kernel
lemma complete_8_5 : CompleteAt 8 5 := by decide +kernel
lemma complete_case8 : ∀ e0, CompleteAt 8 e0 := by
  intro e0
  fin_cases e0
  · exact complete_8_0
  · exact complete_8_1
  · exact complete_8_2
  · exact complete_8_3
  · exact complete_8_4
  · exact complete_8_5
#print axioms complete_case8
end Erdos184Work.PureSixLocalFilter4
