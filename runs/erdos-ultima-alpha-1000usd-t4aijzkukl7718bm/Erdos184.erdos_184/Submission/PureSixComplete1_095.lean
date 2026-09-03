import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_95_0 : CompleteAt 95 0 := by decide +kernel
lemma complete_95_1 : CompleteAt 95 1 := by decide +kernel
lemma complete_95_2 : CompleteAt 95 2 := by decide +kernel
lemma complete_95_3 : CompleteAt 95 3 := by decide +kernel
lemma complete_95_4 : CompleteAt 95 4 := by decide +kernel
lemma complete_case95 : ∀ e0, CompleteAt 95 e0 := by
  intro e0
  fin_cases e0
  · exact complete_95_0
  · exact complete_95_1
  · exact complete_95_2
  · exact complete_95_3
  · exact complete_95_4
#print axioms complete_case95
end Erdos184Work.PureSixLocalFilter1
