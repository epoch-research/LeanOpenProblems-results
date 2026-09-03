import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_113_0 : CompleteAt 113 0 := by decide +kernel
lemma complete_113_1 : CompleteAt 113 1 := by decide +kernel
lemma complete_113_2 : CompleteAt 113 2 := by decide +kernel
lemma complete_113_3 : CompleteAt 113 3 := by decide +kernel
lemma complete_113_4 : CompleteAt 113 4 := by decide +kernel
lemma complete_case113 : ∀ e0, CompleteAt 113 e0 := by
  intro e0
  fin_cases e0
  · exact complete_113_0
  · exact complete_113_1
  · exact complete_113_2
  · exact complete_113_3
  · exact complete_113_4
#print axioms complete_case113
end Erdos184Work.PureSixLocalFilter1
