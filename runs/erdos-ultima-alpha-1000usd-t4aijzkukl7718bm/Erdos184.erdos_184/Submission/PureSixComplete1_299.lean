import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_299_0 : CompleteAt 299 0 := by decide +kernel
lemma complete_299_1 : CompleteAt 299 1 := by decide +kernel
lemma complete_299_2 : CompleteAt 299 2 := by decide +kernel
lemma complete_299_3 : CompleteAt 299 3 := by decide +kernel
lemma complete_299_4 : CompleteAt 299 4 := by decide +kernel
lemma complete_case299 : ∀ e0, CompleteAt 299 e0 := by
  intro e0
  fin_cases e0
  · exact complete_299_0
  · exact complete_299_1
  · exact complete_299_2
  · exact complete_299_3
  · exact complete_299_4
#print axioms complete_case299
end Erdos184Work.PureSixLocalFilter1
