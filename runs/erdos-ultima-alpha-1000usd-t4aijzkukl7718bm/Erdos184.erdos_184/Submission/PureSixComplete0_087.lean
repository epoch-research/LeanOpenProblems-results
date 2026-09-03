import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_87_0 : CompleteAt 87 0 := by decide +kernel
lemma complete_87_1 : CompleteAt 87 1 := by decide +kernel
lemma complete_87_2 : CompleteAt 87 2 := by decide +kernel
lemma complete_87_3 : CompleteAt 87 3 := by decide +kernel
lemma complete_case87 : ∀ e0, CompleteAt 87 e0 := by
  intro e0
  fin_cases e0
  · exact complete_87_0
  · exact complete_87_1
  · exact complete_87_2
  · exact complete_87_3
#print axioms complete_case87
end Erdos184Work.PureSixLocalFilter0
