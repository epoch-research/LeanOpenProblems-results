import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_330_0 : CompleteAt 330 0 := by decide +kernel
lemma complete_330_1 : CompleteAt 330 1 := by decide +kernel
lemma complete_330_2 : CompleteAt 330 2 := by decide +kernel
lemma complete_330_3 : CompleteAt 330 3 := by decide +kernel
lemma complete_330_4 : CompleteAt 330 4 := by decide +kernel
lemma complete_case330 : ∀ e0, CompleteAt 330 e0 := by
  intro e0
  fin_cases e0
  · exact complete_330_0
  · exact complete_330_1
  · exact complete_330_2
  · exact complete_330_3
  · exact complete_330_4
#print axioms complete_case330
end Erdos184Work.PureSixLocalFilter1
