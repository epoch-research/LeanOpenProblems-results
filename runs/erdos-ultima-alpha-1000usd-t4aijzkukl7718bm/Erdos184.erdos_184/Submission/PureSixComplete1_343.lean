import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_343_0 : CompleteAt 343 0 := by decide +kernel
lemma complete_343_1 : CompleteAt 343 1 := by decide +kernel
lemma complete_343_2 : CompleteAt 343 2 := by decide +kernel
lemma complete_343_3 : CompleteAt 343 3 := by decide +kernel
lemma complete_343_4 : CompleteAt 343 4 := by decide +kernel
lemma complete_case343 : ∀ e0, CompleteAt 343 e0 := by
  intro e0
  fin_cases e0
  · exact complete_343_0
  · exact complete_343_1
  · exact complete_343_2
  · exact complete_343_3
  · exact complete_343_4
#print axioms complete_case343
end Erdos184Work.PureSixLocalFilter1
