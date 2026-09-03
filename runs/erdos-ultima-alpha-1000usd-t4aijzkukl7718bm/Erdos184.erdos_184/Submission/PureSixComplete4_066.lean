import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_66_0 : CompleteAt 66 0 := by decide +kernel
lemma complete_66_1 : CompleteAt 66 1 := by decide +kernel
lemma complete_66_2 : CompleteAt 66 2 := by decide +kernel
lemma complete_66_3 : CompleteAt 66 3 := by decide +kernel
lemma complete_66_4 : CompleteAt 66 4 := by decide +kernel
lemma complete_66_5 : CompleteAt 66 5 := by decide +kernel
lemma complete_case66 : ∀ e0, CompleteAt 66 e0 := by
  intro e0
  fin_cases e0
  · exact complete_66_0
  · exact complete_66_1
  · exact complete_66_2
  · exact complete_66_3
  · exact complete_66_4
  · exact complete_66_5
#print axioms complete_case66
end Erdos184Work.PureSixLocalFilter4
