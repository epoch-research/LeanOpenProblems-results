import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_184_0 : CompleteAt 184 0 := by decide +kernel
lemma complete_184_1 : CompleteAt 184 1 := by decide +kernel
lemma complete_184_2 : CompleteAt 184 2 := by decide +kernel
lemma complete_184_3 : CompleteAt 184 3 := by decide +kernel
lemma complete_184_4 : CompleteAt 184 4 := by decide +kernel
lemma complete_case184 : ∀ e0, CompleteAt 184 e0 := by
  intro e0
  fin_cases e0
  · exact complete_184_0
  · exact complete_184_1
  · exact complete_184_2
  · exact complete_184_3
  · exact complete_184_4
#print axioms complete_case184
end Erdos184Work.PureSixLocalFilter1
