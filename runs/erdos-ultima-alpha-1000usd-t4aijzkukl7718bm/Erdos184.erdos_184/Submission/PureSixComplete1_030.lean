import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_30_0 : CompleteAt 30 0 := by decide +kernel
lemma complete_30_1 : CompleteAt 30 1 := by decide +kernel
lemma complete_30_2 : CompleteAt 30 2 := by decide +kernel
lemma complete_30_3 : CompleteAt 30 3 := by decide +kernel
lemma complete_30_4 : CompleteAt 30 4 := by decide +kernel
lemma complete_case30 : ∀ e0, CompleteAt 30 e0 := by
  intro e0
  fin_cases e0
  · exact complete_30_0
  · exact complete_30_1
  · exact complete_30_2
  · exact complete_30_3
  · exact complete_30_4
#print axioms complete_case30
end Erdos184Work.PureSixLocalFilter1
