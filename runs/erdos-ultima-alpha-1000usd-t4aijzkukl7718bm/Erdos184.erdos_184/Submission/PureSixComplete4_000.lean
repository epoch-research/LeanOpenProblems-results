import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_0_0 : CompleteAt 0 0 := by decide +kernel
lemma complete_0_1 : CompleteAt 0 1 := by decide +kernel
lemma complete_0_2 : CompleteAt 0 2 := by decide +kernel
lemma complete_0_3 : CompleteAt 0 3 := by decide +kernel
lemma complete_0_4 : CompleteAt 0 4 := by decide +kernel
lemma complete_0_5 : CompleteAt 0 5 := by decide +kernel
lemma complete_case0 : ∀ e0, CompleteAt 0 e0 := by
  intro e0
  fin_cases e0
  · exact complete_0_0
  · exact complete_0_1
  · exact complete_0_2
  · exact complete_0_3
  · exact complete_0_4
  · exact complete_0_5
#print axioms complete_case0
end Erdos184Work.PureSixLocalFilter4
