import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_118_0 : CompleteAt 118 0 := by decide +kernel
lemma complete_118_1 : CompleteAt 118 1 := by decide +kernel
lemma complete_118_2 : CompleteAt 118 2 := by decide +kernel
lemma complete_118_3 : CompleteAt 118 3 := by decide +kernel
lemma complete_case118 : ∀ e0, CompleteAt 118 e0 := by
  intro e0
  fin_cases e0
  · exact complete_118_0
  · exact complete_118_1
  · exact complete_118_2
  · exact complete_118_3
#print axioms complete_case118
end Erdos184Work.PureSixLocalFilter0
