import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_230_0 : CompleteAt 230 0 := by decide +kernel
lemma complete_230_1 : CompleteAt 230 1 := by decide +kernel
lemma complete_230_2 : CompleteAt 230 2 := by decide +kernel
lemma complete_230_3 : CompleteAt 230 3 := by decide +kernel
lemma complete_230_4 : CompleteAt 230 4 := by decide +kernel
lemma complete_case230 : ∀ e0, CompleteAt 230 e0 := by
  intro e0
  fin_cases e0
  · exact complete_230_0
  · exact complete_230_1
  · exact complete_230_2
  · exact complete_230_3
  · exact complete_230_4
#print axioms complete_case230
end Erdos184Work.PureSixLocalFilter1
