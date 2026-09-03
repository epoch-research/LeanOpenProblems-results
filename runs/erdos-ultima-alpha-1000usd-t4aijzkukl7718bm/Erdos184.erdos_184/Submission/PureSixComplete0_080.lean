import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_80_0 : CompleteAt 80 0 := by decide +kernel
lemma complete_80_1 : CompleteAt 80 1 := by decide +kernel
lemma complete_80_2 : CompleteAt 80 2 := by decide +kernel
lemma complete_80_3 : CompleteAt 80 3 := by decide +kernel
lemma complete_case80 : ∀ e0, CompleteAt 80 e0 := by
  intro e0
  fin_cases e0
  · exact complete_80_0
  · exact complete_80_1
  · exact complete_80_2
  · exact complete_80_3
#print axioms complete_case80
end Erdos184Work.PureSixLocalFilter0
