import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_195_0 : CompleteAt 195 0 := by decide +kernel
lemma complete_195_1 : CompleteAt 195 1 := by decide +kernel
lemma complete_195_2 : CompleteAt 195 2 := by decide +kernel
lemma complete_195_3 : CompleteAt 195 3 := by decide +kernel
lemma complete_195_4 : CompleteAt 195 4 := by decide +kernel
lemma complete_case195 : ∀ e0, CompleteAt 195 e0 := by
  intro e0
  fin_cases e0
  · exact complete_195_0
  · exact complete_195_1
  · exact complete_195_2
  · exact complete_195_3
  · exact complete_195_4
#print axioms complete_case195
end Erdos184Work.PureSixLocalFilter1
