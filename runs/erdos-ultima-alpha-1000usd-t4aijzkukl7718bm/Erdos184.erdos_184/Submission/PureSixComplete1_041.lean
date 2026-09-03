import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_41_0 : CompleteAt 41 0 := by decide +kernel
lemma complete_41_1 : CompleteAt 41 1 := by decide +kernel
lemma complete_41_2 : CompleteAt 41 2 := by decide +kernel
lemma complete_41_3 : CompleteAt 41 3 := by decide +kernel
lemma complete_41_4 : CompleteAt 41 4 := by decide +kernel
lemma complete_case41 : ∀ e0, CompleteAt 41 e0 := by
  intro e0
  fin_cases e0
  · exact complete_41_0
  · exact complete_41_1
  · exact complete_41_2
  · exact complete_41_3
  · exact complete_41_4
#print axioms complete_case41
end Erdos184Work.PureSixLocalFilter1
