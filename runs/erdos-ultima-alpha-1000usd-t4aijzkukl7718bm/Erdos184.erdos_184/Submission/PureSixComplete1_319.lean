import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_319_0 : CompleteAt 319 0 := by decide +kernel
lemma complete_319_1 : CompleteAt 319 1 := by decide +kernel
lemma complete_319_2 : CompleteAt 319 2 := by decide +kernel
lemma complete_319_3 : CompleteAt 319 3 := by decide +kernel
lemma complete_319_4 : CompleteAt 319 4 := by decide +kernel
lemma complete_case319 : ∀ e0, CompleteAt 319 e0 := by
  intro e0
  fin_cases e0
  · exact complete_319_0
  · exact complete_319_1
  · exact complete_319_2
  · exact complete_319_3
  · exact complete_319_4
#print axioms complete_case319
end Erdos184Work.PureSixLocalFilter1
