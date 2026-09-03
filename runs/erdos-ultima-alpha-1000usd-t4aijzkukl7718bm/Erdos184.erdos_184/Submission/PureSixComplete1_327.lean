import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_327_0 : CompleteAt 327 0 := by decide +kernel
lemma complete_327_1 : CompleteAt 327 1 := by decide +kernel
lemma complete_327_2 : CompleteAt 327 2 := by decide +kernel
lemma complete_327_3 : CompleteAt 327 3 := by decide +kernel
lemma complete_327_4 : CompleteAt 327 4 := by decide +kernel
lemma complete_case327 : ∀ e0, CompleteAt 327 e0 := by
  intro e0
  fin_cases e0
  · exact complete_327_0
  · exact complete_327_1
  · exact complete_327_2
  · exact complete_327_3
  · exact complete_327_4
#print axioms complete_case327
end Erdos184Work.PureSixLocalFilter1
