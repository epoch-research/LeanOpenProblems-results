import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_291_0 : CompleteAt 291 0 := by decide +kernel
lemma complete_291_1 : CompleteAt 291 1 := by decide +kernel
lemma complete_291_2 : CompleteAt 291 2 := by decide +kernel
lemma complete_291_3 : CompleteAt 291 3 := by decide +kernel
lemma complete_291_4 : CompleteAt 291 4 := by decide +kernel
lemma complete_case291 : ∀ e0, CompleteAt 291 e0 := by
  intro e0
  fin_cases e0
  · exact complete_291_0
  · exact complete_291_1
  · exact complete_291_2
  · exact complete_291_3
  · exact complete_291_4
#print axioms complete_case291
end Erdos184Work.PureSixLocalFilter1
