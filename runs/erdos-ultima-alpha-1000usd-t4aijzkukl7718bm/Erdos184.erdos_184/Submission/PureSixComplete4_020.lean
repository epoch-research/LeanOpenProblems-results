import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_20_0 : CompleteAt 20 0 := by decide +kernel
lemma complete_20_1 : CompleteAt 20 1 := by decide +kernel
lemma complete_20_2 : CompleteAt 20 2 := by decide +kernel
lemma complete_20_3 : CompleteAt 20 3 := by decide +kernel
lemma complete_20_4 : CompleteAt 20 4 := by decide +kernel
lemma complete_20_5 : CompleteAt 20 5 := by decide +kernel
lemma complete_case20 : ∀ e0, CompleteAt 20 e0 := by
  intro e0
  fin_cases e0
  · exact complete_20_0
  · exact complete_20_1
  · exact complete_20_2
  · exact complete_20_3
  · exact complete_20_4
  · exact complete_20_5
#print axioms complete_case20
end Erdos184Work.PureSixLocalFilter4
