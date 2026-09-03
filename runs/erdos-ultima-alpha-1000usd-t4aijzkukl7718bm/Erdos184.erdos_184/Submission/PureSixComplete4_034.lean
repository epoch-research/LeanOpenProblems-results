import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_34_0 : CompleteAt 34 0 := by decide +kernel
lemma complete_34_1 : CompleteAt 34 1 := by decide +kernel
lemma complete_34_2 : CompleteAt 34 2 := by decide +kernel
lemma complete_34_3 : CompleteAt 34 3 := by decide +kernel
lemma complete_34_4 : CompleteAt 34 4 := by decide +kernel
lemma complete_34_5 : CompleteAt 34 5 := by decide +kernel
lemma complete_case34 : ∀ e0, CompleteAt 34 e0 := by
  intro e0
  fin_cases e0
  · exact complete_34_0
  · exact complete_34_1
  · exact complete_34_2
  · exact complete_34_3
  · exact complete_34_4
  · exact complete_34_5
#print axioms complete_case34
end Erdos184Work.PureSixLocalFilter4
