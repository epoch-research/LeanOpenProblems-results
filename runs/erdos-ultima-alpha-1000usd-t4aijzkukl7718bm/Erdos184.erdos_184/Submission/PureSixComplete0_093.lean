import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_93_0 : CompleteAt 93 0 := by decide +kernel
lemma complete_93_1 : CompleteAt 93 1 := by decide +kernel
lemma complete_93_2 : CompleteAt 93 2 := by decide +kernel
lemma complete_93_3 : CompleteAt 93 3 := by decide +kernel
lemma complete_case93 : ∀ e0, CompleteAt 93 e0 := by
  intro e0
  fin_cases e0
  · exact complete_93_0
  · exact complete_93_1
  · exact complete_93_2
  · exact complete_93_3
#print axioms complete_case93
end Erdos184Work.PureSixLocalFilter0
