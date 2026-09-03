import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_15_0 : CompleteAt 15 0 := by decide +kernel
lemma complete_15_1 : CompleteAt 15 1 := by decide +kernel
lemma complete_15_2 : CompleteAt 15 2 := by decide +kernel
lemma complete_15_3 : CompleteAt 15 3 := by decide +kernel
lemma complete_15_4 : CompleteAt 15 4 := by decide +kernel
lemma complete_case15 : ∀ e0, CompleteAt 15 e0 := by
  intro e0
  fin_cases e0
  · exact complete_15_0
  · exact complete_15_1
  · exact complete_15_2
  · exact complete_15_3
  · exact complete_15_4
#print axioms complete_case15
end Erdos184Work.PureSixLocalFilter1
