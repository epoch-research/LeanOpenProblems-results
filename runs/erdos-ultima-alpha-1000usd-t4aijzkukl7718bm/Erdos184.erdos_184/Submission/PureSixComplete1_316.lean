import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_316_0 : CompleteAt 316 0 := by decide +kernel
lemma complete_316_1 : CompleteAt 316 1 := by decide +kernel
lemma complete_316_2 : CompleteAt 316 2 := by decide +kernel
lemma complete_316_3 : CompleteAt 316 3 := by decide +kernel
lemma complete_316_4 : CompleteAt 316 4 := by decide +kernel
lemma complete_case316 : ∀ e0, CompleteAt 316 e0 := by
  intro e0
  fin_cases e0
  · exact complete_316_0
  · exact complete_316_1
  · exact complete_316_2
  · exact complete_316_3
  · exact complete_316_4
#print axioms complete_case316
end Erdos184Work.PureSixLocalFilter1
