import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_120_0 : CompleteAt 120 0 := by decide +kernel
lemma complete_120_1 : CompleteAt 120 1 := by decide +kernel
lemma complete_120_2 : CompleteAt 120 2 := by decide +kernel
lemma complete_120_3 : CompleteAt 120 3 := by decide +kernel
lemma complete_120_4 : CompleteAt 120 4 := by decide +kernel
lemma complete_case120 : ∀ e0, CompleteAt 120 e0 := by
  intro e0
  fin_cases e0
  · exact complete_120_0
  · exact complete_120_1
  · exact complete_120_2
  · exact complete_120_3
  · exact complete_120_4
#print axioms complete_case120
end Erdos184Work.PureSixLocalFilter1
