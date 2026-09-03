import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_14_0 : CompleteAt 14 0 := by decide +kernel
lemma complete_14_1 : CompleteAt 14 1 := by decide +kernel
lemma complete_14_2 : CompleteAt 14 2 := by decide +kernel
lemma complete_14_3 : CompleteAt 14 3 := by decide +kernel
lemma complete_14_4 : CompleteAt 14 4 := by decide +kernel
lemma complete_14_5 : CompleteAt 14 5 := by decide +kernel
lemma complete_case14 : ∀ e0, CompleteAt 14 e0 := by
  intro e0
  fin_cases e0
  · exact complete_14_0
  · exact complete_14_1
  · exact complete_14_2
  · exact complete_14_3
  · exact complete_14_4
  · exact complete_14_5
#print axioms complete_case14
end Erdos184Work.PureSixLocalFilter4
