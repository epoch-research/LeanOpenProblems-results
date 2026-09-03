import Submission.PureSixLocalFilter2
namespace Erdos184Work.PureSixLocalFilter2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_3_0 : CompleteAt 3 0 := by decide +kernel
lemma complete_3_1 : CompleteAt 3 1 := by decide +kernel
lemma complete_3_2 : CompleteAt 3 2 := by decide +kernel
lemma complete_3_3 : CompleteAt 3 3 := by decide +kernel
lemma complete_3_4 : CompleteAt 3 4 := by decide +kernel
lemma complete_case3 : ∀ e0, CompleteAt 3 e0 := by
  intro e0
  fin_cases e0
  · exact complete_3_0
  · exact complete_3_1
  · exact complete_3_2
  · exact complete_3_3
  · exact complete_3_4
#print axioms complete_case3
end Erdos184Work.PureSixLocalFilter2
