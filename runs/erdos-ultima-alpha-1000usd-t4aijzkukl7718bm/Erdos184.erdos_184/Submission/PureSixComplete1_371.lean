import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_371_0 : CompleteAt 371 0 := by decide +kernel
lemma complete_371_1 : CompleteAt 371 1 := by decide +kernel
lemma complete_371_2 : CompleteAt 371 2 := by decide +kernel
lemma complete_371_3 : CompleteAt 371 3 := by decide +kernel
lemma complete_371_4 : CompleteAt 371 4 := by decide +kernel
lemma complete_case371 : ∀ e0, CompleteAt 371 e0 := by
  intro e0
  fin_cases e0
  · exact complete_371_0
  · exact complete_371_1
  · exact complete_371_2
  · exact complete_371_3
  · exact complete_371_4
#print axioms complete_case371
end Erdos184Work.PureSixLocalFilter1
