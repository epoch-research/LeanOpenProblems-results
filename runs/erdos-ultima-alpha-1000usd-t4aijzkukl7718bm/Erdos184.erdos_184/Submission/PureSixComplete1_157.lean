import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_157_0 : CompleteAt 157 0 := by decide +kernel
lemma complete_157_1 : CompleteAt 157 1 := by decide +kernel
lemma complete_157_2 : CompleteAt 157 2 := by decide +kernel
lemma complete_157_3 : CompleteAt 157 3 := by decide +kernel
lemma complete_157_4 : CompleteAt 157 4 := by decide +kernel
lemma complete_case157 : ∀ e0, CompleteAt 157 e0 := by
  intro e0
  fin_cases e0
  · exact complete_157_0
  · exact complete_157_1
  · exact complete_157_2
  · exact complete_157_3
  · exact complete_157_4
#print axioms complete_case157
end Erdos184Work.PureSixLocalFilter1
