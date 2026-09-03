import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_306_0 : CompleteAt 306 0 := by decide +kernel
lemma complete_306_1 : CompleteAt 306 1 := by decide +kernel
lemma complete_306_2 : CompleteAt 306 2 := by decide +kernel
lemma complete_306_3 : CompleteAt 306 3 := by decide +kernel
lemma complete_306_4 : CompleteAt 306 4 := by decide +kernel
lemma complete_case306 : ∀ e0, CompleteAt 306 e0 := by
  intro e0
  fin_cases e0
  · exact complete_306_0
  · exact complete_306_1
  · exact complete_306_2
  · exact complete_306_3
  · exact complete_306_4
#print axioms complete_case306
end Erdos184Work.PureSixLocalFilter1
