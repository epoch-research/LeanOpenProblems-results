import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_206_0 : CompleteAt 206 0 := by decide +kernel
lemma complete_206_1 : CompleteAt 206 1 := by decide +kernel
lemma complete_206_2 : CompleteAt 206 2 := by decide +kernel
lemma complete_206_3 : CompleteAt 206 3 := by decide +kernel
lemma complete_206_4 : CompleteAt 206 4 := by decide +kernel
lemma complete_case206 : ∀ e0, CompleteAt 206 e0 := by
  intro e0
  fin_cases e0
  · exact complete_206_0
  · exact complete_206_1
  · exact complete_206_2
  · exact complete_206_3
  · exact complete_206_4
#print axioms complete_case206
end Erdos184Work.PureSixLocalFilter1
