import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_359_0 : CompleteAt 359 0 := by decide +kernel
lemma complete_359_1 : CompleteAt 359 1 := by decide +kernel
lemma complete_359_2 : CompleteAt 359 2 := by decide +kernel
lemma complete_359_3 : CompleteAt 359 3 := by decide +kernel
lemma complete_359_4 : CompleteAt 359 4 := by decide +kernel
lemma complete_case359 : ∀ e0, CompleteAt 359 e0 := by
  intro e0
  fin_cases e0
  · exact complete_359_0
  · exact complete_359_1
  · exact complete_359_2
  · exact complete_359_3
  · exact complete_359_4
#print axioms complete_case359
end Erdos184Work.PureSixLocalFilter1
