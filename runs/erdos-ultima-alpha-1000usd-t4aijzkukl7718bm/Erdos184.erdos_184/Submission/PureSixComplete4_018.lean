import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_18_0 : CompleteAt 18 0 := by decide +kernel
lemma complete_18_1 : CompleteAt 18 1 := by decide +kernel
lemma complete_18_2 : CompleteAt 18 2 := by decide +kernel
lemma complete_18_3 : CompleteAt 18 3 := by decide +kernel
lemma complete_18_4 : CompleteAt 18 4 := by decide +kernel
lemma complete_18_5 : CompleteAt 18 5 := by decide +kernel
lemma complete_case18 : ∀ e0, CompleteAt 18 e0 := by
  intro e0
  fin_cases e0
  · exact complete_18_0
  · exact complete_18_1
  · exact complete_18_2
  · exact complete_18_3
  · exact complete_18_4
  · exact complete_18_5
#print axioms complete_case18
end Erdos184Work.PureSixLocalFilter4
