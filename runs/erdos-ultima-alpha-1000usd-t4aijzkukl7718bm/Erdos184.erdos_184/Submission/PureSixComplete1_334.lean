import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_334_0 : CompleteAt 334 0 := by decide +kernel
lemma complete_334_1 : CompleteAt 334 1 := by decide +kernel
lemma complete_334_2 : CompleteAt 334 2 := by decide +kernel
lemma complete_334_3 : CompleteAt 334 3 := by decide +kernel
lemma complete_334_4 : CompleteAt 334 4 := by decide +kernel
lemma complete_case334 : ∀ e0, CompleteAt 334 e0 := by
  intro e0
  fin_cases e0
  · exact complete_334_0
  · exact complete_334_1
  · exact complete_334_2
  · exact complete_334_3
  · exact complete_334_4
#print axioms complete_case334
end Erdos184Work.PureSixLocalFilter1
