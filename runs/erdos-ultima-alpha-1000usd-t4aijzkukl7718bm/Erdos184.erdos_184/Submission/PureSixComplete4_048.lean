import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_48_0 : CompleteAt 48 0 := by decide +kernel
lemma complete_48_1 : CompleteAt 48 1 := by decide +kernel
lemma complete_48_2 : CompleteAt 48 2 := by decide +kernel
lemma complete_48_3 : CompleteAt 48 3 := by decide +kernel
lemma complete_48_4 : CompleteAt 48 4 := by decide +kernel
lemma complete_48_5 : CompleteAt 48 5 := by decide +kernel
lemma complete_case48 : ∀ e0, CompleteAt 48 e0 := by
  intro e0
  fin_cases e0
  · exact complete_48_0
  · exact complete_48_1
  · exact complete_48_2
  · exact complete_48_3
  · exact complete_48_4
  · exact complete_48_5
#print axioms complete_case48
end Erdos184Work.PureSixLocalFilter4
