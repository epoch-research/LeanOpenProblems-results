import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_33_0 : CompleteAt 33 0 := by decide +kernel
lemma complete_33_1 : CompleteAt 33 1 := by decide +kernel
lemma complete_33_2 : CompleteAt 33 2 := by decide +kernel
lemma complete_33_3 : CompleteAt 33 3 := by decide +kernel
lemma complete_33_4 : CompleteAt 33 4 := by decide +kernel
lemma complete_case33 : ∀ e0, CompleteAt 33 e0 := by
  intro e0
  fin_cases e0
  · exact complete_33_0
  · exact complete_33_1
  · exact complete_33_2
  · exact complete_33_3
  · exact complete_33_4
#print axioms complete_case33
end Erdos184Work.PureSixLocalFilter1
