import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_187_0 : CompleteAt 187 0 := by decide +kernel
lemma complete_187_1 : CompleteAt 187 1 := by decide +kernel
lemma complete_187_2 : CompleteAt 187 2 := by decide +kernel
lemma complete_187_3 : CompleteAt 187 3 := by decide +kernel
lemma complete_187_4 : CompleteAt 187 4 := by decide +kernel
lemma complete_case187 : ∀ e0, CompleteAt 187 e0 := by
  intro e0
  fin_cases e0
  · exact complete_187_0
  · exact complete_187_1
  · exact complete_187_2
  · exact complete_187_3
  · exact complete_187_4
#print axioms complete_case187
end Erdos184Work.PureSixLocalFilter1
