import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_131_0 : CompleteAt 131 0 := by decide +kernel
lemma complete_131_1 : CompleteAt 131 1 := by decide +kernel
lemma complete_131_2 : CompleteAt 131 2 := by decide +kernel
lemma complete_131_3 : CompleteAt 131 3 := by decide +kernel
lemma complete_case131 : ∀ e0, CompleteAt 131 e0 := by
  intro e0
  fin_cases e0
  · exact complete_131_0
  · exact complete_131_1
  · exact complete_131_2
  · exact complete_131_3
#print axioms complete_case131
end Erdos184Work.PureSixLocalFilter0
