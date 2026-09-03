import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_53_0 : CompleteAt 53 0 := by decide +kernel
lemma complete_53_1 : CompleteAt 53 1 := by decide +kernel
lemma complete_53_2 : CompleteAt 53 2 := by decide +kernel
lemma complete_53_3 : CompleteAt 53 3 := by decide +kernel
lemma complete_53_4 : CompleteAt 53 4 := by decide +kernel
lemma complete_case53 : ∀ e0, CompleteAt 53 e0 := by
  intro e0
  fin_cases e0
  · exact complete_53_0
  · exact complete_53_1
  · exact complete_53_2
  · exact complete_53_3
  · exact complete_53_4
#print axioms complete_case53
end Erdos184Work.PureSixLocalFilter1
