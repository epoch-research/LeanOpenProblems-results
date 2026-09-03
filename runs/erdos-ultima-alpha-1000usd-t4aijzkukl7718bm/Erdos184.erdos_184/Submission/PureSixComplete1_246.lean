import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_246_0 : CompleteAt 246 0 := by decide +kernel
lemma complete_246_1 : CompleteAt 246 1 := by decide +kernel
lemma complete_246_2 : CompleteAt 246 2 := by decide +kernel
lemma complete_246_3 : CompleteAt 246 3 := by decide +kernel
lemma complete_246_4 : CompleteAt 246 4 := by decide +kernel
lemma complete_case246 : ∀ e0, CompleteAt 246 e0 := by
  intro e0
  fin_cases e0
  · exact complete_246_0
  · exact complete_246_1
  · exact complete_246_2
  · exact complete_246_3
  · exact complete_246_4
#print axioms complete_case246
end Erdos184Work.PureSixLocalFilter1
