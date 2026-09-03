import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_304_0 : CompleteAt 304 0 := by decide +kernel
lemma complete_304_1 : CompleteAt 304 1 := by decide +kernel
lemma complete_304_2 : CompleteAt 304 2 := by decide +kernel
lemma complete_304_3 : CompleteAt 304 3 := by decide +kernel
lemma complete_304_4 : CompleteAt 304 4 := by decide +kernel
lemma complete_case304 : ∀ e0, CompleteAt 304 e0 := by
  intro e0
  fin_cases e0
  · exact complete_304_0
  · exact complete_304_1
  · exact complete_304_2
  · exact complete_304_3
  · exact complete_304_4
#print axioms complete_case304
end Erdos184Work.PureSixLocalFilter1
