import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_379_0 : CompleteAt 379 0 := by decide +kernel
lemma complete_379_1 : CompleteAt 379 1 := by decide +kernel
lemma complete_379_2 : CompleteAt 379 2 := by decide +kernel
lemma complete_379_3 : CompleteAt 379 3 := by decide +kernel
lemma complete_379_4 : CompleteAt 379 4 := by decide +kernel
lemma complete_case379 : ∀ e0, CompleteAt 379 e0 := by
  intro e0
  fin_cases e0
  · exact complete_379_0
  · exact complete_379_1
  · exact complete_379_2
  · exact complete_379_3
  · exact complete_379_4
#print axioms complete_case379
end Erdos184Work.PureSixLocalFilter1
