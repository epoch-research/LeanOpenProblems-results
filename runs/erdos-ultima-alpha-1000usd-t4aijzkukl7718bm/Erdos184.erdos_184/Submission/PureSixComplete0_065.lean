import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_65_0 : CompleteAt 65 0 := by decide +kernel
lemma complete_65_1 : CompleteAt 65 1 := by decide +kernel
lemma complete_65_2 : CompleteAt 65 2 := by decide +kernel
lemma complete_65_3 : CompleteAt 65 3 := by decide +kernel
lemma complete_case65 : ∀ e0, CompleteAt 65 e0 := by
  intro e0
  fin_cases e0
  · exact complete_65_0
  · exact complete_65_1
  · exact complete_65_2
  · exact complete_65_3
#print axioms complete_case65
end Erdos184Work.PureSixLocalFilter0
