import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_17_0 : CompleteAt 17 0 := by decide +kernel
lemma complete_17_1 : CompleteAt 17 1 := by decide +kernel
lemma complete_17_2 : CompleteAt 17 2 := by decide +kernel
lemma complete_17_3 : CompleteAt 17 3 := by decide +kernel
lemma complete_17_4 : CompleteAt 17 4 := by decide +kernel
lemma complete_case17 : ∀ e0, CompleteAt 17 e0 := by
  intro e0
  fin_cases e0
  · exact complete_17_0
  · exact complete_17_1
  · exact complete_17_2
  · exact complete_17_3
  · exact complete_17_4
#print axioms complete_case17
end Erdos184Work.PureSixLocalFilter1
