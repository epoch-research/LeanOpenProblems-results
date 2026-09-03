import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_297_0 : CompleteAt 297 0 := by decide +kernel
lemma complete_297_1 : CompleteAt 297 1 := by decide +kernel
lemma complete_297_2 : CompleteAt 297 2 := by decide +kernel
lemma complete_297_3 : CompleteAt 297 3 := by decide +kernel
lemma complete_297_4 : CompleteAt 297 4 := by decide +kernel
lemma complete_case297 : ∀ e0, CompleteAt 297 e0 := by
  intro e0
  fin_cases e0
  · exact complete_297_0
  · exact complete_297_1
  · exact complete_297_2
  · exact complete_297_3
  · exact complete_297_4
#print axioms complete_case297
end Erdos184Work.PureSixLocalFilter1
