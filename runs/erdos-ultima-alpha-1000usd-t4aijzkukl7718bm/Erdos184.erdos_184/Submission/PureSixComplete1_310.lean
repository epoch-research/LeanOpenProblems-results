import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_310_0 : CompleteAt 310 0 := by decide +kernel
lemma complete_310_1 : CompleteAt 310 1 := by decide +kernel
lemma complete_310_2 : CompleteAt 310 2 := by decide +kernel
lemma complete_310_3 : CompleteAt 310 3 := by decide +kernel
lemma complete_310_4 : CompleteAt 310 4 := by decide +kernel
lemma complete_case310 : ∀ e0, CompleteAt 310 e0 := by
  intro e0
  fin_cases e0
  · exact complete_310_0
  · exact complete_310_1
  · exact complete_310_2
  · exact complete_310_3
  · exact complete_310_4
#print axioms complete_case310
end Erdos184Work.PureSixLocalFilter1
