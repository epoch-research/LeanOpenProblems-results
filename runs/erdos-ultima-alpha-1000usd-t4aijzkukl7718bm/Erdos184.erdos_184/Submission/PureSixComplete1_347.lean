import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_347_0 : CompleteAt 347 0 := by decide +kernel
lemma complete_347_1 : CompleteAt 347 1 := by decide +kernel
lemma complete_347_2 : CompleteAt 347 2 := by decide +kernel
lemma complete_347_3 : CompleteAt 347 3 := by decide +kernel
lemma complete_347_4 : CompleteAt 347 4 := by decide +kernel
lemma complete_case347 : ∀ e0, CompleteAt 347 e0 := by
  intro e0
  fin_cases e0
  · exact complete_347_0
  · exact complete_347_1
  · exact complete_347_2
  · exact complete_347_3
  · exact complete_347_4
#print axioms complete_case347
end Erdos184Work.PureSixLocalFilter1
