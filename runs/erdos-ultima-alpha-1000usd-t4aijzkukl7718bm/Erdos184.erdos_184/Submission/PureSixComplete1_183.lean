import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_183_0 : CompleteAt 183 0 := by decide +kernel
lemma complete_183_1 : CompleteAt 183 1 := by decide +kernel
lemma complete_183_2 : CompleteAt 183 2 := by decide +kernel
lemma complete_183_3 : CompleteAt 183 3 := by decide +kernel
lemma complete_183_4 : CompleteAt 183 4 := by decide +kernel
lemma complete_case183 : ∀ e0, CompleteAt 183 e0 := by
  intro e0
  fin_cases e0
  · exact complete_183_0
  · exact complete_183_1
  · exact complete_183_2
  · exact complete_183_3
  · exact complete_183_4
#print axioms complete_case183
end Erdos184Work.PureSixLocalFilter1
