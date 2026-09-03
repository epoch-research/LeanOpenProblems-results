import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_226_0 : CompleteAt 226 0 := by decide +kernel
lemma complete_226_1 : CompleteAt 226 1 := by decide +kernel
lemma complete_226_2 : CompleteAt 226 2 := by decide +kernel
lemma complete_226_3 : CompleteAt 226 3 := by decide +kernel
lemma complete_226_4 : CompleteAt 226 4 := by decide +kernel
lemma complete_case226 : ∀ e0, CompleteAt 226 e0 := by
  intro e0
  fin_cases e0
  · exact complete_226_0
  · exact complete_226_1
  · exact complete_226_2
  · exact complete_226_3
  · exact complete_226_4
#print axioms complete_case226
end Erdos184Work.PureSixLocalFilter1
