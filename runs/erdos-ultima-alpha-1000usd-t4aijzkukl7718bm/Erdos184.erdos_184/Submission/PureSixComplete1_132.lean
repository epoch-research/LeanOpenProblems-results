import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_132_0 : CompleteAt 132 0 := by decide +kernel
lemma complete_132_1 : CompleteAt 132 1 := by decide +kernel
lemma complete_132_2 : CompleteAt 132 2 := by decide +kernel
lemma complete_132_3 : CompleteAt 132 3 := by decide +kernel
lemma complete_132_4 : CompleteAt 132 4 := by decide +kernel
lemma complete_case132 : ∀ e0, CompleteAt 132 e0 := by
  intro e0
  fin_cases e0
  · exact complete_132_0
  · exact complete_132_1
  · exact complete_132_2
  · exact complete_132_3
  · exact complete_132_4
#print axioms complete_case132
end Erdos184Work.PureSixLocalFilter1
