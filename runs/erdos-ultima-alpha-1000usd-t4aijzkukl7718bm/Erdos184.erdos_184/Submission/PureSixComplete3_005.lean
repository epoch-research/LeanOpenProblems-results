import Submission.PureSixLocalFilter3
namespace Erdos184Work.PureSixLocalFilter3
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_5_0 : CompleteAt 5 0 := by decide +kernel
lemma complete_5_1 : CompleteAt 5 1 := by decide +kernel
lemma complete_5_2 : CompleteAt 5 2 := by decide +kernel
lemma complete_5_3 : CompleteAt 5 3 := by decide +kernel
lemma complete_5_4 : CompleteAt 5 4 := by decide +kernel
lemma complete_case5 : ∀ e0, CompleteAt 5 e0 := by
  intro e0
  fin_cases e0
  · exact complete_5_0
  · exact complete_5_1
  · exact complete_5_2
  · exact complete_5_3
  · exact complete_5_4
#print axioms complete_case5
end Erdos184Work.PureSixLocalFilter3
