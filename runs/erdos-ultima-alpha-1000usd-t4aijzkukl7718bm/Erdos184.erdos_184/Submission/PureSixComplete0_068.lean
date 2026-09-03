import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_68_0 : CompleteAt 68 0 := by decide +kernel
lemma complete_68_1 : CompleteAt 68 1 := by decide +kernel
lemma complete_68_2 : CompleteAt 68 2 := by decide +kernel
lemma complete_68_3 : CompleteAt 68 3 := by decide +kernel
lemma complete_case68 : ∀ e0, CompleteAt 68 e0 := by
  intro e0
  fin_cases e0
  · exact complete_68_0
  · exact complete_68_1
  · exact complete_68_2
  · exact complete_68_3
#print axioms complete_case68
end Erdos184Work.PureSixLocalFilter0
