import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_107_0 : CompleteAt 107 0 := by decide +kernel
lemma complete_107_1 : CompleteAt 107 1 := by decide +kernel
lemma complete_107_2 : CompleteAt 107 2 := by decide +kernel
lemma complete_107_3 : CompleteAt 107 3 := by decide +kernel
lemma complete_case107 : ∀ e0, CompleteAt 107 e0 := by
  intro e0
  fin_cases e0
  · exact complete_107_0
  · exact complete_107_1
  · exact complete_107_2
  · exact complete_107_3
#print axioms complete_case107
end Erdos184Work.PureSixLocalFilter0
