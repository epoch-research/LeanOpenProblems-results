import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_82_0 : CompleteAt 82 0 := by decide +kernel
lemma complete_82_1 : CompleteAt 82 1 := by decide +kernel
lemma complete_82_2 : CompleteAt 82 2 := by decide +kernel
lemma complete_82_3 : CompleteAt 82 3 := by decide +kernel
lemma complete_82_4 : CompleteAt 82 4 := by decide +kernel
lemma complete_case82 : ∀ e0, CompleteAt 82 e0 := by
  intro e0
  fin_cases e0
  · exact complete_82_0
  · exact complete_82_1
  · exact complete_82_2
  · exact complete_82_3
  · exact complete_82_4
#print axioms complete_case82
end Erdos184Work.PureSixLocalFilter1
