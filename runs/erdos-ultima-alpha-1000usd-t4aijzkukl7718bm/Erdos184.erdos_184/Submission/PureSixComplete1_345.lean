import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_345_0 : CompleteAt 345 0 := by decide +kernel
lemma complete_345_1 : CompleteAt 345 1 := by decide +kernel
lemma complete_345_2 : CompleteAt 345 2 := by decide +kernel
lemma complete_345_3 : CompleteAt 345 3 := by decide +kernel
lemma complete_345_4 : CompleteAt 345 4 := by decide +kernel
lemma complete_case345 : ∀ e0, CompleteAt 345 e0 := by
  intro e0
  fin_cases e0
  · exact complete_345_0
  · exact complete_345_1
  · exact complete_345_2
  · exact complete_345_3
  · exact complete_345_4
#print axioms complete_case345
end Erdos184Work.PureSixLocalFilter1
