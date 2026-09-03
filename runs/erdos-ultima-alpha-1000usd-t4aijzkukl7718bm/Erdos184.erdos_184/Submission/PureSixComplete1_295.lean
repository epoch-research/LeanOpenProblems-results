import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_295_0 : CompleteAt 295 0 := by decide +kernel
lemma complete_295_1 : CompleteAt 295 1 := by decide +kernel
lemma complete_295_2 : CompleteAt 295 2 := by decide +kernel
lemma complete_295_3 : CompleteAt 295 3 := by decide +kernel
lemma complete_295_4 : CompleteAt 295 4 := by decide +kernel
lemma complete_case295 : ∀ e0, CompleteAt 295 e0 := by
  intro e0
  fin_cases e0
  · exact complete_295_0
  · exact complete_295_1
  · exact complete_295_2
  · exact complete_295_3
  · exact complete_295_4
#print axioms complete_case295
end Erdos184Work.PureSixLocalFilter1
