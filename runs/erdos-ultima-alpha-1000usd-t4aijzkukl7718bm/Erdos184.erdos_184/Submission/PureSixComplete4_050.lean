import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_50_0 : CompleteAt 50 0 := by decide +kernel
lemma complete_50_1 : CompleteAt 50 1 := by decide +kernel
lemma complete_50_2 : CompleteAt 50 2 := by decide +kernel
lemma complete_50_3 : CompleteAt 50 3 := by decide +kernel
lemma complete_50_4 : CompleteAt 50 4 := by decide +kernel
lemma complete_50_5 : CompleteAt 50 5 := by decide +kernel
lemma complete_case50 : ∀ e0, CompleteAt 50 e0 := by
  intro e0
  fin_cases e0
  · exact complete_50_0
  · exact complete_50_1
  · exact complete_50_2
  · exact complete_50_3
  · exact complete_50_4
  · exact complete_50_5
#print axioms complete_case50
end Erdos184Work.PureSixLocalFilter4
