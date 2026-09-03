import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_381_0 : CompleteAt 381 0 := by decide +kernel
lemma complete_381_1 : CompleteAt 381 1 := by decide +kernel
lemma complete_381_2 : CompleteAt 381 2 := by decide +kernel
lemma complete_381_3 : CompleteAt 381 3 := by decide +kernel
lemma complete_381_4 : CompleteAt 381 4 := by decide +kernel
lemma complete_case381 : ∀ e0, CompleteAt 381 e0 := by
  intro e0
  fin_cases e0
  · exact complete_381_0
  · exact complete_381_1
  · exact complete_381_2
  · exact complete_381_3
  · exact complete_381_4
#print axioms complete_case381
end Erdos184Work.PureSixLocalFilter1
