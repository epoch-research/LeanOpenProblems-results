import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_364_0 : CompleteAt 364 0 := by decide +kernel
lemma complete_364_1 : CompleteAt 364 1 := by decide +kernel
lemma complete_364_2 : CompleteAt 364 2 := by decide +kernel
lemma complete_364_3 : CompleteAt 364 3 := by decide +kernel
lemma complete_364_4 : CompleteAt 364 4 := by decide +kernel
lemma complete_case364 : ∀ e0, CompleteAt 364 e0 := by
  intro e0
  fin_cases e0
  · exact complete_364_0
  · exact complete_364_1
  · exact complete_364_2
  · exact complete_364_3
  · exact complete_364_4
#print axioms complete_case364
end Erdos184Work.PureSixLocalFilter1
