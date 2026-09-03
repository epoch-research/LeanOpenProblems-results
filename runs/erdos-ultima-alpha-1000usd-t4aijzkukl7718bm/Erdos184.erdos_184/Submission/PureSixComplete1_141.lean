import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_141_0 : CompleteAt 141 0 := by decide +kernel
lemma complete_141_1 : CompleteAt 141 1 := by decide +kernel
lemma complete_141_2 : CompleteAt 141 2 := by decide +kernel
lemma complete_141_3 : CompleteAt 141 3 := by decide +kernel
lemma complete_141_4 : CompleteAt 141 4 := by decide +kernel
lemma complete_case141 : ∀ e0, CompleteAt 141 e0 := by
  intro e0
  fin_cases e0
  · exact complete_141_0
  · exact complete_141_1
  · exact complete_141_2
  · exact complete_141_3
  · exact complete_141_4
#print axioms complete_case141
end Erdos184Work.PureSixLocalFilter1
