import Submission.PureSixLocalFilter3
namespace Erdos184Work.PureSixLocalFilter3
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_1_0 : CompleteAt 1 0 := by decide +kernel
lemma complete_1_1 : CompleteAt 1 1 := by decide +kernel
lemma complete_1_2 : CompleteAt 1 2 := by decide +kernel
lemma complete_1_3 : CompleteAt 1 3 := by decide +kernel
lemma complete_1_4 : CompleteAt 1 4 := by decide +kernel
lemma complete_case1 : ∀ e0, CompleteAt 1 e0 := by
  intro e0
  fin_cases e0
  · exact complete_1_0
  · exact complete_1_1
  · exact complete_1_2
  · exact complete_1_3
  · exact complete_1_4
#print axioms complete_case1
end Erdos184Work.PureSixLocalFilter3
