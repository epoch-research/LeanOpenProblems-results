import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_61_0 : CompleteAt 61 0 := by decide +kernel
lemma complete_61_1 : CompleteAt 61 1 := by decide +kernel
lemma complete_61_2 : CompleteAt 61 2 := by decide +kernel
lemma complete_61_3 : CompleteAt 61 3 := by decide +kernel
lemma complete_61_4 : CompleteAt 61 4 := by decide +kernel
lemma complete_61_5 : CompleteAt 61 5 := by decide +kernel
lemma complete_case61 : ∀ e0, CompleteAt 61 e0 := by
  intro e0
  fin_cases e0
  · exact complete_61_0
  · exact complete_61_1
  · exact complete_61_2
  · exact complete_61_3
  · exact complete_61_4
  · exact complete_61_5
#print axioms complete_case61
end Erdos184Work.PureSixLocalFilter4
