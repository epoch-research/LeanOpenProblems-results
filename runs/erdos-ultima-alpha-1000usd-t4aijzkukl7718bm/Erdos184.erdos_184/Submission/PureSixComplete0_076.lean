import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_76_0 : CompleteAt 76 0 := by decide +kernel
lemma complete_76_1 : CompleteAt 76 1 := by decide +kernel
lemma complete_76_2 : CompleteAt 76 2 := by decide +kernel
lemma complete_76_3 : CompleteAt 76 3 := by decide +kernel
lemma complete_case76 : ∀ e0, CompleteAt 76 e0 := by
  intro e0
  fin_cases e0
  · exact complete_76_0
  · exact complete_76_1
  · exact complete_76_2
  · exact complete_76_3
#print axioms complete_case76
end Erdos184Work.PureSixLocalFilter0
