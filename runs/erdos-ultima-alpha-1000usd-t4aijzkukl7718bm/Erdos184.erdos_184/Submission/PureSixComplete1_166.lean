import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_166_0 : CompleteAt 166 0 := by decide +kernel
lemma complete_166_1 : CompleteAt 166 1 := by decide +kernel
lemma complete_166_2 : CompleteAt 166 2 := by decide +kernel
lemma complete_166_3 : CompleteAt 166 3 := by decide +kernel
lemma complete_166_4 : CompleteAt 166 4 := by decide +kernel
lemma complete_case166 : ∀ e0, CompleteAt 166 e0 := by
  intro e0
  fin_cases e0
  · exact complete_166_0
  · exact complete_166_1
  · exact complete_166_2
  · exact complete_166_3
  · exact complete_166_4
#print axioms complete_case166
end Erdos184Work.PureSixLocalFilter1
