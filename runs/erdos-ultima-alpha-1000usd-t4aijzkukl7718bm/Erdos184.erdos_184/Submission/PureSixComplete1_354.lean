import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_354_0 : CompleteAt 354 0 := by decide +kernel
lemma complete_354_1 : CompleteAt 354 1 := by decide +kernel
lemma complete_354_2 : CompleteAt 354 2 := by decide +kernel
lemma complete_354_3 : CompleteAt 354 3 := by decide +kernel
lemma complete_354_4 : CompleteAt 354 4 := by decide +kernel
lemma complete_case354 : ∀ e0, CompleteAt 354 e0 := by
  intro e0
  fin_cases e0
  · exact complete_354_0
  · exact complete_354_1
  · exact complete_354_2
  · exact complete_354_3
  · exact complete_354_4
#print axioms complete_case354
end Erdos184Work.PureSixLocalFilter1
