import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_37_0 : CompleteAt 37 0 := by decide +kernel
lemma complete_37_1 : CompleteAt 37 1 := by decide +kernel
lemma complete_37_2 : CompleteAt 37 2 := by decide +kernel
lemma complete_37_3 : CompleteAt 37 3 := by decide +kernel
lemma complete_37_4 : CompleteAt 37 4 := by decide +kernel
lemma complete_case37 : ∀ e0, CompleteAt 37 e0 := by
  intro e0
  fin_cases e0
  · exact complete_37_0
  · exact complete_37_1
  · exact complete_37_2
  · exact complete_37_3
  · exact complete_37_4
#print axioms complete_case37
end Erdos184Work.PureSixLocalFilter1
