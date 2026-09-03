import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_40_0 : CompleteAt 40 0 := by decide +kernel
lemma complete_40_1 : CompleteAt 40 1 := by decide +kernel
lemma complete_40_2 : CompleteAt 40 2 := by decide +kernel
lemma complete_40_3 : CompleteAt 40 3 := by decide +kernel
lemma complete_40_4 : CompleteAt 40 4 := by decide +kernel
lemma complete_case40 : ∀ e0, CompleteAt 40 e0 := by
  intro e0
  fin_cases e0
  · exact complete_40_0
  · exact complete_40_1
  · exact complete_40_2
  · exact complete_40_3
  · exact complete_40_4
#print axioms complete_case40
end Erdos184Work.PureSixLocalFilter1
