import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_321_0 : CompleteAt 321 0 := by decide +kernel
lemma complete_321_1 : CompleteAt 321 1 := by decide +kernel
lemma complete_321_2 : CompleteAt 321 2 := by decide +kernel
lemma complete_321_3 : CompleteAt 321 3 := by decide +kernel
lemma complete_321_4 : CompleteAt 321 4 := by decide +kernel
lemma complete_case321 : ∀ e0, CompleteAt 321 e0 := by
  intro e0
  fin_cases e0
  · exact complete_321_0
  · exact complete_321_1
  · exact complete_321_2
  · exact complete_321_3
  · exact complete_321_4
#print axioms complete_case321
end Erdos184Work.PureSixLocalFilter1
