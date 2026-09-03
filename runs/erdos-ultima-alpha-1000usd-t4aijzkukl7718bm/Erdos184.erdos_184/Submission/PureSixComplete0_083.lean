import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_83_0 : CompleteAt 83 0 := by decide +kernel
lemma complete_83_1 : CompleteAt 83 1 := by decide +kernel
lemma complete_83_2 : CompleteAt 83 2 := by decide +kernel
lemma complete_83_3 : CompleteAt 83 3 := by decide +kernel
lemma complete_case83 : ∀ e0, CompleteAt 83 e0 := by
  intro e0
  fin_cases e0
  · exact complete_83_0
  · exact complete_83_1
  · exact complete_83_2
  · exact complete_83_3
#print axioms complete_case83
end Erdos184Work.PureSixLocalFilter0
