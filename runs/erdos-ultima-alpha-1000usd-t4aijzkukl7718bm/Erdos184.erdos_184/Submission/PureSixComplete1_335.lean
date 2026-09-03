import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_335_0 : CompleteAt 335 0 := by decide +kernel
lemma complete_335_1 : CompleteAt 335 1 := by decide +kernel
lemma complete_335_2 : CompleteAt 335 2 := by decide +kernel
lemma complete_335_3 : CompleteAt 335 3 := by decide +kernel
lemma complete_335_4 : CompleteAt 335 4 := by decide +kernel
lemma complete_case335 : ∀ e0, CompleteAt 335 e0 := by
  intro e0
  fin_cases e0
  · exact complete_335_0
  · exact complete_335_1
  · exact complete_335_2
  · exact complete_335_3
  · exact complete_335_4
#print axioms complete_case335
end Erdos184Work.PureSixLocalFilter1
