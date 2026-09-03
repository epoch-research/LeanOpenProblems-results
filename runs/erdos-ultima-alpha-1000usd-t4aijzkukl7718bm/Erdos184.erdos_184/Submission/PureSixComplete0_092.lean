import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_92_0 : CompleteAt 92 0 := by decide +kernel
lemma complete_92_1 : CompleteAt 92 1 := by decide +kernel
lemma complete_92_2 : CompleteAt 92 2 := by decide +kernel
lemma complete_92_3 : CompleteAt 92 3 := by decide +kernel
lemma complete_case92 : ∀ e0, CompleteAt 92 e0 := by
  intro e0
  fin_cases e0
  · exact complete_92_0
  · exact complete_92_1
  · exact complete_92_2
  · exact complete_92_3
#print axioms complete_case92
end Erdos184Work.PureSixLocalFilter0
