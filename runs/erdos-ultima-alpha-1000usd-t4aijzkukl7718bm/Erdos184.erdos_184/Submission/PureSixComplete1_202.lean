import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_202_0 : CompleteAt 202 0 := by decide +kernel
lemma complete_202_1 : CompleteAt 202 1 := by decide +kernel
lemma complete_202_2 : CompleteAt 202 2 := by decide +kernel
lemma complete_202_3 : CompleteAt 202 3 := by decide +kernel
lemma complete_202_4 : CompleteAt 202 4 := by decide +kernel
lemma complete_case202 : ∀ e0, CompleteAt 202 e0 := by
  intro e0
  fin_cases e0
  · exact complete_202_0
  · exact complete_202_1
  · exact complete_202_2
  · exact complete_202_3
  · exact complete_202_4
#print axioms complete_case202
end Erdos184Work.PureSixLocalFilter1
