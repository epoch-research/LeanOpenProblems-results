import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_103_0 : CompleteAt 103 0 := by decide +kernel
lemma complete_103_1 : CompleteAt 103 1 := by decide +kernel
lemma complete_103_2 : CompleteAt 103 2 := by decide +kernel
lemma complete_103_3 : CompleteAt 103 3 := by decide +kernel
lemma complete_case103 : ∀ e0, CompleteAt 103 e0 := by
  intro e0
  fin_cases e0
  · exact complete_103_0
  · exact complete_103_1
  · exact complete_103_2
  · exact complete_103_3
#print axioms complete_case103
end Erdos184Work.PureSixLocalFilter0
