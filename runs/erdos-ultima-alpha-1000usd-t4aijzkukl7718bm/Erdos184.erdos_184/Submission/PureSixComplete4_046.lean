import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_46_0 : CompleteAt 46 0 := by decide +kernel
lemma complete_46_1 : CompleteAt 46 1 := by decide +kernel
lemma complete_46_2 : CompleteAt 46 2 := by decide +kernel
lemma complete_46_3 : CompleteAt 46 3 := by decide +kernel
lemma complete_46_4 : CompleteAt 46 4 := by decide +kernel
lemma complete_46_5 : CompleteAt 46 5 := by decide +kernel
lemma complete_case46 : ∀ e0, CompleteAt 46 e0 := by
  intro e0
  fin_cases e0
  · exact complete_46_0
  · exact complete_46_1
  · exact complete_46_2
  · exact complete_46_3
  · exact complete_46_4
  · exact complete_46_5
#print axioms complete_case46
end Erdos184Work.PureSixLocalFilter4
