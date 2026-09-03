import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_360_0 : CompleteAt 360 0 := by decide +kernel
lemma complete_360_1 : CompleteAt 360 1 := by decide +kernel
lemma complete_360_2 : CompleteAt 360 2 := by decide +kernel
lemma complete_360_3 : CompleteAt 360 3 := by decide +kernel
lemma complete_360_4 : CompleteAt 360 4 := by decide +kernel
lemma complete_case360 : ∀ e0, CompleteAt 360 e0 := by
  intro e0
  fin_cases e0
  · exact complete_360_0
  · exact complete_360_1
  · exact complete_360_2
  · exact complete_360_3
  · exact complete_360_4
#print axioms complete_case360
end Erdos184Work.PureSixLocalFilter1
