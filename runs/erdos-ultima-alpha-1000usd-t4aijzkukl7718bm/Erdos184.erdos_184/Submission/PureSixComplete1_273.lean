import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_273_0 : CompleteAt 273 0 := by decide +kernel
lemma complete_273_1 : CompleteAt 273 1 := by decide +kernel
lemma complete_273_2 : CompleteAt 273 2 := by decide +kernel
lemma complete_273_3 : CompleteAt 273 3 := by decide +kernel
lemma complete_273_4 : CompleteAt 273 4 := by decide +kernel
lemma complete_case273 : ∀ e0, CompleteAt 273 e0 := by
  intro e0
  fin_cases e0
  · exact complete_273_0
  · exact complete_273_1
  · exact complete_273_2
  · exact complete_273_3
  · exact complete_273_4
#print axioms complete_case273
end Erdos184Work.PureSixLocalFilter1
