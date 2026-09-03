import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_342_0 : CompleteAt 342 0 := by decide +kernel
lemma complete_342_1 : CompleteAt 342 1 := by decide +kernel
lemma complete_342_2 : CompleteAt 342 2 := by decide +kernel
lemma complete_342_3 : CompleteAt 342 3 := by decide +kernel
lemma complete_342_4 : CompleteAt 342 4 := by decide +kernel
lemma complete_case342 : ∀ e0, CompleteAt 342 e0 := by
  intro e0
  fin_cases e0
  · exact complete_342_0
  · exact complete_342_1
  · exact complete_342_2
  · exact complete_342_3
  · exact complete_342_4
#print axioms complete_case342
end Erdos184Work.PureSixLocalFilter1
