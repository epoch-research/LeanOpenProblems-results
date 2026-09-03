import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_190_0 : CompleteAt 190 0 := by decide +kernel
lemma complete_190_1 : CompleteAt 190 1 := by decide +kernel
lemma complete_190_2 : CompleteAt 190 2 := by decide +kernel
lemma complete_190_3 : CompleteAt 190 3 := by decide +kernel
lemma complete_190_4 : CompleteAt 190 4 := by decide +kernel
lemma complete_case190 : ∀ e0, CompleteAt 190 e0 := by
  intro e0
  fin_cases e0
  · exact complete_190_0
  · exact complete_190_1
  · exact complete_190_2
  · exact complete_190_3
  · exact complete_190_4
#print axioms complete_case190
end Erdos184Work.PureSixLocalFilter1
