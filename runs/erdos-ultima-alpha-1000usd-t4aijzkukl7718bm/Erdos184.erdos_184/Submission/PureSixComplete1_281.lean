import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_281_0 : CompleteAt 281 0 := by decide +kernel
lemma complete_281_1 : CompleteAt 281 1 := by decide +kernel
lemma complete_281_2 : CompleteAt 281 2 := by decide +kernel
lemma complete_281_3 : CompleteAt 281 3 := by decide +kernel
lemma complete_281_4 : CompleteAt 281 4 := by decide +kernel
lemma complete_case281 : ∀ e0, CompleteAt 281 e0 := by
  intro e0
  fin_cases e0
  · exact complete_281_0
  · exact complete_281_1
  · exact complete_281_2
  · exact complete_281_3
  · exact complete_281_4
#print axioms complete_case281
end Erdos184Work.PureSixLocalFilter1
