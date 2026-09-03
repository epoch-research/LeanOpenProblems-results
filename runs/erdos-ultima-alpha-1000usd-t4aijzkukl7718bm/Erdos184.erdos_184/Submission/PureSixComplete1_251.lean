import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_251_0 : CompleteAt 251 0 := by decide +kernel
lemma complete_251_1 : CompleteAt 251 1 := by decide +kernel
lemma complete_251_2 : CompleteAt 251 2 := by decide +kernel
lemma complete_251_3 : CompleteAt 251 3 := by decide +kernel
lemma complete_251_4 : CompleteAt 251 4 := by decide +kernel
lemma complete_case251 : ∀ e0, CompleteAt 251 e0 := by
  intro e0
  fin_cases e0
  · exact complete_251_0
  · exact complete_251_1
  · exact complete_251_2
  · exact complete_251_3
  · exact complete_251_4
#print axioms complete_case251
end Erdos184Work.PureSixLocalFilter1
