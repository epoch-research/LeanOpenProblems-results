import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_171_0 : CompleteAt 171 0 := by decide +kernel
lemma complete_171_1 : CompleteAt 171 1 := by decide +kernel
lemma complete_171_2 : CompleteAt 171 2 := by decide +kernel
lemma complete_171_3 : CompleteAt 171 3 := by decide +kernel
lemma complete_171_4 : CompleteAt 171 4 := by decide +kernel
lemma complete_case171 : ∀ e0, CompleteAt 171 e0 := by
  intro e0
  fin_cases e0
  · exact complete_171_0
  · exact complete_171_1
  · exact complete_171_2
  · exact complete_171_3
  · exact complete_171_4
#print axioms complete_case171
end Erdos184Work.PureSixLocalFilter1
