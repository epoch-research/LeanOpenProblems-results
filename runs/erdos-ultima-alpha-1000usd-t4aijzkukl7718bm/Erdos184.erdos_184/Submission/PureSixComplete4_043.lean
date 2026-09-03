import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_43_0 : CompleteAt 43 0 := by decide +kernel
lemma complete_43_1 : CompleteAt 43 1 := by decide +kernel
lemma complete_43_2 : CompleteAt 43 2 := by decide +kernel
lemma complete_43_3 : CompleteAt 43 3 := by decide +kernel
lemma complete_43_4 : CompleteAt 43 4 := by decide +kernel
lemma complete_43_5 : CompleteAt 43 5 := by decide +kernel
lemma complete_case43 : ∀ e0, CompleteAt 43 e0 := by
  intro e0
  fin_cases e0
  · exact complete_43_0
  · exact complete_43_1
  · exact complete_43_2
  · exact complete_43_3
  · exact complete_43_4
  · exact complete_43_5
#print axioms complete_case43
end Erdos184Work.PureSixLocalFilter4
