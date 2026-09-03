import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_105_0 : CompleteAt 105 0 := by decide +kernel
lemma complete_105_1 : CompleteAt 105 1 := by decide +kernel
lemma complete_105_2 : CompleteAt 105 2 := by decide +kernel
lemma complete_105_3 : CompleteAt 105 3 := by decide +kernel
lemma complete_case105 : ∀ e0, CompleteAt 105 e0 := by
  intro e0
  fin_cases e0
  · exact complete_105_0
  · exact complete_105_1
  · exact complete_105_2
  · exact complete_105_3
#print axioms complete_case105
end Erdos184Work.PureSixLocalFilter0
