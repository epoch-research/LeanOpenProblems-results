import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_286_0 : CompleteAt 286 0 := by decide +kernel
lemma complete_286_1 : CompleteAt 286 1 := by decide +kernel
lemma complete_286_2 : CompleteAt 286 2 := by decide +kernel
lemma complete_286_3 : CompleteAt 286 3 := by decide +kernel
lemma complete_286_4 : CompleteAt 286 4 := by decide +kernel
lemma complete_case286 : ∀ e0, CompleteAt 286 e0 := by
  intro e0
  fin_cases e0
  · exact complete_286_0
  · exact complete_286_1
  · exact complete_286_2
  · exact complete_286_3
  · exact complete_286_4
#print axioms complete_case286
end Erdos184Work.PureSixLocalFilter1
