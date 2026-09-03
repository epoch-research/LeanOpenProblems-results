import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_72_0 : CompleteAt 72 0 := by decide +kernel
lemma complete_72_1 : CompleteAt 72 1 := by decide +kernel
lemma complete_72_2 : CompleteAt 72 2 := by decide +kernel
lemma complete_72_3 : CompleteAt 72 3 := by decide +kernel
lemma complete_72_4 : CompleteAt 72 4 := by decide +kernel
lemma complete_72_5 : CompleteAt 72 5 := by decide +kernel
lemma complete_case72 : ∀ e0, CompleteAt 72 e0 := by
  intro e0
  fin_cases e0
  · exact complete_72_0
  · exact complete_72_1
  · exact complete_72_2
  · exact complete_72_3
  · exact complete_72_4
  · exact complete_72_5
#print axioms complete_case72
end Erdos184Work.PureSixLocalFilter4
