import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_127_0 : CompleteAt 127 0 := by decide +kernel
lemma complete_127_1 : CompleteAt 127 1 := by decide +kernel
lemma complete_127_2 : CompleteAt 127 2 := by decide +kernel
lemma complete_127_3 : CompleteAt 127 3 := by decide +kernel
lemma complete_127_4 : CompleteAt 127 4 := by decide +kernel
lemma complete_case127 : ∀ e0, CompleteAt 127 e0 := by
  intro e0
  fin_cases e0
  · exact complete_127_0
  · exact complete_127_1
  · exact complete_127_2
  · exact complete_127_3
  · exact complete_127_4
#print axioms complete_case127
end Erdos184Work.PureSixLocalFilter1
