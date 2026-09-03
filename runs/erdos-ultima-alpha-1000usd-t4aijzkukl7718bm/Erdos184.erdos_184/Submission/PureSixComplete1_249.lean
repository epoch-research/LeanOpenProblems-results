import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_249_0 : CompleteAt 249 0 := by decide +kernel
lemma complete_249_1 : CompleteAt 249 1 := by decide +kernel
lemma complete_249_2 : CompleteAt 249 2 := by decide +kernel
lemma complete_249_3 : CompleteAt 249 3 := by decide +kernel
lemma complete_249_4 : CompleteAt 249 4 := by decide +kernel
lemma complete_case249 : ∀ e0, CompleteAt 249 e0 := by
  intro e0
  fin_cases e0
  · exact complete_249_0
  · exact complete_249_1
  · exact complete_249_2
  · exact complete_249_3
  · exact complete_249_4
#print axioms complete_case249
end Erdos184Work.PureSixLocalFilter1
