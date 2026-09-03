import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_153_0 : CompleteAt 153 0 := by decide +kernel
lemma complete_153_1 : CompleteAt 153 1 := by decide +kernel
lemma complete_153_2 : CompleteAt 153 2 := by decide +kernel
lemma complete_153_3 : CompleteAt 153 3 := by decide +kernel
lemma complete_case153 : ∀ e0, CompleteAt 153 e0 := by
  intro e0
  fin_cases e0
  · exact complete_153_0
  · exact complete_153_1
  · exact complete_153_2
  · exact complete_153_3
#print axioms complete_case153
end Erdos184Work.PureSixLocalFilter0
