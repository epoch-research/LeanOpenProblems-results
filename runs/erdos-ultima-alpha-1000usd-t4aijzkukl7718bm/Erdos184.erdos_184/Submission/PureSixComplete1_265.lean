import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_265_0 : CompleteAt 265 0 := by decide +kernel
lemma complete_265_1 : CompleteAt 265 1 := by decide +kernel
lemma complete_265_2 : CompleteAt 265 2 := by decide +kernel
lemma complete_265_3 : CompleteAt 265 3 := by decide +kernel
lemma complete_265_4 : CompleteAt 265 4 := by decide +kernel
lemma complete_case265 : ∀ e0, CompleteAt 265 e0 := by
  intro e0
  fin_cases e0
  · exact complete_265_0
  · exact complete_265_1
  · exact complete_265_2
  · exact complete_265_3
  · exact complete_265_4
#print axioms complete_case265
end Erdos184Work.PureSixLocalFilter1
