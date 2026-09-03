import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_384_0 : CompleteAt 384 0 := by decide +kernel
lemma complete_384_1 : CompleteAt 384 1 := by decide +kernel
lemma complete_384_2 : CompleteAt 384 2 := by decide +kernel
lemma complete_384_3 : CompleteAt 384 3 := by decide +kernel
lemma complete_384_4 : CompleteAt 384 4 := by decide +kernel
lemma complete_case384 : ∀ e0, CompleteAt 384 e0 := by
  intro e0
  fin_cases e0
  · exact complete_384_0
  · exact complete_384_1
  · exact complete_384_2
  · exact complete_384_3
  · exact complete_384_4
#print axioms complete_case384
end Erdos184Work.PureSixLocalFilter1
