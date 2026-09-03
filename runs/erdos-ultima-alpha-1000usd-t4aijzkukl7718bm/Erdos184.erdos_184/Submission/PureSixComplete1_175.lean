import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_175_0 : CompleteAt 175 0 := by decide +kernel
lemma complete_175_1 : CompleteAt 175 1 := by decide +kernel
lemma complete_175_2 : CompleteAt 175 2 := by decide +kernel
lemma complete_175_3 : CompleteAt 175 3 := by decide +kernel
lemma complete_175_4 : CompleteAt 175 4 := by decide +kernel
lemma complete_case175 : ∀ e0, CompleteAt 175 e0 := by
  intro e0
  fin_cases e0
  · exact complete_175_0
  · exact complete_175_1
  · exact complete_175_2
  · exact complete_175_3
  · exact complete_175_4
#print axioms complete_case175
end Erdos184Work.PureSixLocalFilter1
