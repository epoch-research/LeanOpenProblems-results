import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_57_0 : CompleteAt 57 0 := by decide +kernel
lemma complete_57_1 : CompleteAt 57 1 := by decide +kernel
lemma complete_57_2 : CompleteAt 57 2 := by decide +kernel
lemma complete_57_3 : CompleteAt 57 3 := by decide +kernel
lemma complete_57_4 : CompleteAt 57 4 := by decide +kernel
lemma complete_57_5 : CompleteAt 57 5 := by decide +kernel
lemma complete_case57 : ∀ e0, CompleteAt 57 e0 := by
  intro e0
  fin_cases e0
  · exact complete_57_0
  · exact complete_57_1
  · exact complete_57_2
  · exact complete_57_3
  · exact complete_57_4
  · exact complete_57_5
#print axioms complete_case57
end Erdos184Work.PureSixLocalFilter4
