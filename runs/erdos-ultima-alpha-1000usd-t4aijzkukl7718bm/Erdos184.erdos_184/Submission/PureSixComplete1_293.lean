import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_293_0 : CompleteAt 293 0 := by decide +kernel
lemma complete_293_1 : CompleteAt 293 1 := by decide +kernel
lemma complete_293_2 : CompleteAt 293 2 := by decide +kernel
lemma complete_293_3 : CompleteAt 293 3 := by decide +kernel
lemma complete_293_4 : CompleteAt 293 4 := by decide +kernel
lemma complete_case293 : ∀ e0, CompleteAt 293 e0 := by
  intro e0
  fin_cases e0
  · exact complete_293_0
  · exact complete_293_1
  · exact complete_293_2
  · exact complete_293_3
  · exact complete_293_4
#print axioms complete_case293
end Erdos184Work.PureSixLocalFilter1
