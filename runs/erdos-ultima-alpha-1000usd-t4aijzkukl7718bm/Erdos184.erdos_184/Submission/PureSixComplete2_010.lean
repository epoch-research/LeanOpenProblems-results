import Submission.PureSixLocalFilter2
namespace Erdos184Work.PureSixLocalFilter2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_10_0 : CompleteAt 10 0 := by decide +kernel
lemma complete_10_1 : CompleteAt 10 1 := by decide +kernel
lemma complete_10_2 : CompleteAt 10 2 := by decide +kernel
lemma complete_10_3 : CompleteAt 10 3 := by decide +kernel
lemma complete_10_4 : CompleteAt 10 4 := by decide +kernel
lemma complete_case10 : ∀ e0, CompleteAt 10 e0 := by
  intro e0
  fin_cases e0
  · exact complete_10_0
  · exact complete_10_1
  · exact complete_10_2
  · exact complete_10_3
  · exact complete_10_4
#print axioms complete_case10
end Erdos184Work.PureSixLocalFilter2
