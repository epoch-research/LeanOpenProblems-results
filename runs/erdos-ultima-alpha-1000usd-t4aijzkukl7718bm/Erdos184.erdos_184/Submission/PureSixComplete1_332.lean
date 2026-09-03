import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_332_0 : CompleteAt 332 0 := by decide +kernel
lemma complete_332_1 : CompleteAt 332 1 := by decide +kernel
lemma complete_332_2 : CompleteAt 332 2 := by decide +kernel
lemma complete_332_3 : CompleteAt 332 3 := by decide +kernel
lemma complete_332_4 : CompleteAt 332 4 := by decide +kernel
lemma complete_case332 : ∀ e0, CompleteAt 332 e0 := by
  intro e0
  fin_cases e0
  · exact complete_332_0
  · exact complete_332_1
  · exact complete_332_2
  · exact complete_332_3
  · exact complete_332_4
#print axioms complete_case332
end Erdos184Work.PureSixLocalFilter1
