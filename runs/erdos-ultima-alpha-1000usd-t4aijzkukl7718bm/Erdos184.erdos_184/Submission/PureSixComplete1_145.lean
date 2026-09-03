import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_145_0 : CompleteAt 145 0 := by decide +kernel
lemma complete_145_1 : CompleteAt 145 1 := by decide +kernel
lemma complete_145_2 : CompleteAt 145 2 := by decide +kernel
lemma complete_145_3 : CompleteAt 145 3 := by decide +kernel
lemma complete_145_4 : CompleteAt 145 4 := by decide +kernel
lemma complete_case145 : ∀ e0, CompleteAt 145 e0 := by
  intro e0
  fin_cases e0
  · exact complete_145_0
  · exact complete_145_1
  · exact complete_145_2
  · exact complete_145_3
  · exact complete_145_4
#print axioms complete_case145
end Erdos184Work.PureSixLocalFilter1
