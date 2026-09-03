import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_160_0 : CompleteAt 160 0 := by decide +kernel
lemma complete_160_1 : CompleteAt 160 1 := by decide +kernel
lemma complete_160_2 : CompleteAt 160 2 := by decide +kernel
lemma complete_160_3 : CompleteAt 160 3 := by decide +kernel
lemma complete_160_4 : CompleteAt 160 4 := by decide +kernel
lemma complete_case160 : ∀ e0, CompleteAt 160 e0 := by
  intro e0
  fin_cases e0
  · exact complete_160_0
  · exact complete_160_1
  · exact complete_160_2
  · exact complete_160_3
  · exact complete_160_4
#print axioms complete_case160
end Erdos184Work.PureSixLocalFilter1
