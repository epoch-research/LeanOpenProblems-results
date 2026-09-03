import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_56_0 : CompleteAt 56 0 := by decide +kernel
lemma complete_56_1 : CompleteAt 56 1 := by decide +kernel
lemma complete_56_2 : CompleteAt 56 2 := by decide +kernel
lemma complete_56_3 : CompleteAt 56 3 := by decide +kernel
lemma complete_56_4 : CompleteAt 56 4 := by decide +kernel
lemma complete_case56 : ∀ e0, CompleteAt 56 e0 := by
  intro e0
  fin_cases e0
  · exact complete_56_0
  · exact complete_56_1
  · exact complete_56_2
  · exact complete_56_3
  · exact complete_56_4
#print axioms complete_case56
end Erdos184Work.PureSixLocalFilter1
