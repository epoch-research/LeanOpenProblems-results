import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_389_0 : CompleteAt 389 0 := by decide +kernel
lemma complete_389_1 : CompleteAt 389 1 := by decide +kernel
lemma complete_389_2 : CompleteAt 389 2 := by decide +kernel
lemma complete_389_3 : CompleteAt 389 3 := by decide +kernel
lemma complete_389_4 : CompleteAt 389 4 := by decide +kernel
lemma complete_case389 : ∀ e0, CompleteAt 389 e0 := by
  intro e0
  fin_cases e0
  · exact complete_389_0
  · exact complete_389_1
  · exact complete_389_2
  · exact complete_389_3
  · exact complete_389_4
#print axioms complete_case389
end Erdos184Work.PureSixLocalFilter1
