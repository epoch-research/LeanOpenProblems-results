import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_300_0 : CompleteAt 300 0 := by decide +kernel
lemma complete_300_1 : CompleteAt 300 1 := by decide +kernel
lemma complete_300_2 : CompleteAt 300 2 := by decide +kernel
lemma complete_300_3 : CompleteAt 300 3 := by decide +kernel
lemma complete_300_4 : CompleteAt 300 4 := by decide +kernel
lemma complete_case300 : ∀ e0, CompleteAt 300 e0 := by
  intro e0
  fin_cases e0
  · exact complete_300_0
  · exact complete_300_1
  · exact complete_300_2
  · exact complete_300_3
  · exact complete_300_4
#print axioms complete_case300
end Erdos184Work.PureSixLocalFilter1
