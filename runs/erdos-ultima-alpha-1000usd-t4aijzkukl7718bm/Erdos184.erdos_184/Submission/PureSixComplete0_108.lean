import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_108_0 : CompleteAt 108 0 := by decide +kernel
lemma complete_108_1 : CompleteAt 108 1 := by decide +kernel
lemma complete_108_2 : CompleteAt 108 2 := by decide +kernel
lemma complete_108_3 : CompleteAt 108 3 := by decide +kernel
lemma complete_case108 : ∀ e0, CompleteAt 108 e0 := by
  intro e0
  fin_cases e0
  · exact complete_108_0
  · exact complete_108_1
  · exact complete_108_2
  · exact complete_108_3
#print axioms complete_case108
end Erdos184Work.PureSixLocalFilter0
