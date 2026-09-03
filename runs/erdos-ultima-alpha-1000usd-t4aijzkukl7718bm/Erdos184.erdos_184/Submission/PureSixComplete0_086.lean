import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_86_0 : CompleteAt 86 0 := by decide +kernel
lemma complete_86_1 : CompleteAt 86 1 := by decide +kernel
lemma complete_86_2 : CompleteAt 86 2 := by decide +kernel
lemma complete_86_3 : CompleteAt 86 3 := by decide +kernel
lemma complete_case86 : ∀ e0, CompleteAt 86 e0 := by
  intro e0
  fin_cases e0
  · exact complete_86_0
  · exact complete_86_1
  · exact complete_86_2
  · exact complete_86_3
#print axioms complete_case86
end Erdos184Work.PureSixLocalFilter0
