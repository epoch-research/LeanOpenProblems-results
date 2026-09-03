import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_257_0 : CompleteAt 257 0 := by decide +kernel
lemma complete_257_1 : CompleteAt 257 1 := by decide +kernel
lemma complete_257_2 : CompleteAt 257 2 := by decide +kernel
lemma complete_257_3 : CompleteAt 257 3 := by decide +kernel
lemma complete_257_4 : CompleteAt 257 4 := by decide +kernel
lemma complete_case257 : ∀ e0, CompleteAt 257 e0 := by
  intro e0
  fin_cases e0
  · exact complete_257_0
  · exact complete_257_1
  · exact complete_257_2
  · exact complete_257_3
  · exact complete_257_4
#print axioms complete_case257
end Erdos184Work.PureSixLocalFilter1
