import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_44_0 : CompleteAt 44 0 := by decide +kernel
lemma complete_44_1 : CompleteAt 44 1 := by decide +kernel
lemma complete_44_2 : CompleteAt 44 2 := by decide +kernel
lemma complete_44_3 : CompleteAt 44 3 := by decide +kernel
lemma complete_case44 : ∀ e0, CompleteAt 44 e0 := by
  intro e0
  fin_cases e0
  · exact complete_44_0
  · exact complete_44_1
  · exact complete_44_2
  · exact complete_44_3
#print axioms complete_case44
end Erdos184Work.PureSixLocalFilter0
