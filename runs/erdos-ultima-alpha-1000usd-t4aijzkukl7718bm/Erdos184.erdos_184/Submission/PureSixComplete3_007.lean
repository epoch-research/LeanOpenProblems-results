import Submission.PureSixLocalFilter3
namespace Erdos184Work.PureSixLocalFilter3
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_7_0 : CompleteAt 7 0 := by decide +kernel
lemma complete_7_1 : CompleteAt 7 1 := by decide +kernel
lemma complete_7_2 : CompleteAt 7 2 := by decide +kernel
lemma complete_7_3 : CompleteAt 7 3 := by decide +kernel
lemma complete_7_4 : CompleteAt 7 4 := by decide +kernel
lemma complete_case7 : ∀ e0, CompleteAt 7 e0 := by
  intro e0
  fin_cases e0
  · exact complete_7_0
  · exact complete_7_1
  · exact complete_7_2
  · exact complete_7_3
  · exact complete_7_4
#print axioms complete_case7
end Erdos184Work.PureSixLocalFilter3
