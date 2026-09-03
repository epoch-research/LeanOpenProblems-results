import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_303_0 : CompleteAt 303 0 := by decide +kernel
lemma complete_303_1 : CompleteAt 303 1 := by decide +kernel
lemma complete_303_2 : CompleteAt 303 2 := by decide +kernel
lemma complete_303_3 : CompleteAt 303 3 := by decide +kernel
lemma complete_303_4 : CompleteAt 303 4 := by decide +kernel
lemma complete_case303 : ∀ e0, CompleteAt 303 e0 := by
  intro e0
  fin_cases e0
  · exact complete_303_0
  · exact complete_303_1
  · exact complete_303_2
  · exact complete_303_3
  · exact complete_303_4
#print axioms complete_case303
end Erdos184Work.PureSixLocalFilter1
