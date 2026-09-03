import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_179_0 : CompleteAt 179 0 := by decide +kernel
lemma complete_179_1 : CompleteAt 179 1 := by decide +kernel
lemma complete_179_2 : CompleteAt 179 2 := by decide +kernel
lemma complete_179_3 : CompleteAt 179 3 := by decide +kernel
lemma complete_179_4 : CompleteAt 179 4 := by decide +kernel
lemma complete_case179 : ∀ e0, CompleteAt 179 e0 := by
  intro e0
  fin_cases e0
  · exact complete_179_0
  · exact complete_179_1
  · exact complete_179_2
  · exact complete_179_3
  · exact complete_179_4
#print axioms complete_case179
end Erdos184Work.PureSixLocalFilter1
