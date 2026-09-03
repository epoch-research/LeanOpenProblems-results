import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_367_0 : CompleteAt 367 0 := by decide +kernel
lemma complete_367_1 : CompleteAt 367 1 := by decide +kernel
lemma complete_367_2 : CompleteAt 367 2 := by decide +kernel
lemma complete_367_3 : CompleteAt 367 3 := by decide +kernel
lemma complete_367_4 : CompleteAt 367 4 := by decide +kernel
lemma complete_case367 : ∀ e0, CompleteAt 367 e0 := by
  intro e0
  fin_cases e0
  · exact complete_367_0
  · exact complete_367_1
  · exact complete_367_2
  · exact complete_367_3
  · exact complete_367_4
#print axioms complete_case367
end Erdos184Work.PureSixLocalFilter1
