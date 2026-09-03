import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_323_0 : CompleteAt 323 0 := by decide +kernel
lemma complete_323_1 : CompleteAt 323 1 := by decide +kernel
lemma complete_323_2 : CompleteAt 323 2 := by decide +kernel
lemma complete_323_3 : CompleteAt 323 3 := by decide +kernel
lemma complete_323_4 : CompleteAt 323 4 := by decide +kernel
lemma complete_case323 : ∀ e0, CompleteAt 323 e0 := by
  intro e0
  fin_cases e0
  · exact complete_323_0
  · exact complete_323_1
  · exact complete_323_2
  · exact complete_323_3
  · exact complete_323_4
#print axioms complete_case323
end Erdos184Work.PureSixLocalFilter1
