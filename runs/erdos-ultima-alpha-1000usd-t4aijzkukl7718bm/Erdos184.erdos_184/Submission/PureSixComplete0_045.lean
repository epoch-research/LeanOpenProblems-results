import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_45_0 : CompleteAt 45 0 := by decide +kernel
lemma complete_45_1 : CompleteAt 45 1 := by decide +kernel
lemma complete_45_2 : CompleteAt 45 2 := by decide +kernel
lemma complete_45_3 : CompleteAt 45 3 := by decide +kernel
lemma complete_case45 : ∀ e0, CompleteAt 45 e0 := by
  intro e0
  fin_cases e0
  · exact complete_45_0
  · exact complete_45_1
  · exact complete_45_2
  · exact complete_45_3
#print axioms complete_case45
end Erdos184Work.PureSixLocalFilter0
