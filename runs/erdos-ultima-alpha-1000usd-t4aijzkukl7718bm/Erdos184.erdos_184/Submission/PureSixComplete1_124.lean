import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_124_0 : CompleteAt 124 0 := by decide +kernel
lemma complete_124_1 : CompleteAt 124 1 := by decide +kernel
lemma complete_124_2 : CompleteAt 124 2 := by decide +kernel
lemma complete_124_3 : CompleteAt 124 3 := by decide +kernel
lemma complete_124_4 : CompleteAt 124 4 := by decide +kernel
lemma complete_case124 : ∀ e0, CompleteAt 124 e0 := by
  intro e0
  fin_cases e0
  · exact complete_124_0
  · exact complete_124_1
  · exact complete_124_2
  · exact complete_124_3
  · exact complete_124_4
#print axioms complete_case124
end Erdos184Work.PureSixLocalFilter1
