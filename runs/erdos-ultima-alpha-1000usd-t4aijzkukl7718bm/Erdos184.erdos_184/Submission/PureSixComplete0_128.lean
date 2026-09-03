import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_128_0 : CompleteAt 128 0 := by decide +kernel
lemma complete_128_1 : CompleteAt 128 1 := by decide +kernel
lemma complete_128_2 : CompleteAt 128 2 := by decide +kernel
lemma complete_128_3 : CompleteAt 128 3 := by decide +kernel
lemma complete_case128 : ∀ e0, CompleteAt 128 e0 := by
  intro e0
  fin_cases e0
  · exact complete_128_0
  · exact complete_128_1
  · exact complete_128_2
  · exact complete_128_3
#print axioms complete_case128
end Erdos184Work.PureSixLocalFilter0
