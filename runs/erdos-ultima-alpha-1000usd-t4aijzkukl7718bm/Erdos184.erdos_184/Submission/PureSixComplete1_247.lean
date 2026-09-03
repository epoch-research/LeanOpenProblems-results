import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_247_0 : CompleteAt 247 0 := by decide +kernel
lemma complete_247_1 : CompleteAt 247 1 := by decide +kernel
lemma complete_247_2 : CompleteAt 247 2 := by decide +kernel
lemma complete_247_3 : CompleteAt 247 3 := by decide +kernel
lemma complete_247_4 : CompleteAt 247 4 := by decide +kernel
lemma complete_case247 : ∀ e0, CompleteAt 247 e0 := by
  intro e0
  fin_cases e0
  · exact complete_247_0
  · exact complete_247_1
  · exact complete_247_2
  · exact complete_247_3
  · exact complete_247_4
#print axioms complete_case247
end Erdos184Work.PureSixLocalFilter1
