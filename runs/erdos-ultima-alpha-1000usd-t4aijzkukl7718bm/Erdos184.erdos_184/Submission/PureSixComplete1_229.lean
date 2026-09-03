import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_229_0 : CompleteAt 229 0 := by decide +kernel
lemma complete_229_1 : CompleteAt 229 1 := by decide +kernel
lemma complete_229_2 : CompleteAt 229 2 := by decide +kernel
lemma complete_229_3 : CompleteAt 229 3 := by decide +kernel
lemma complete_229_4 : CompleteAt 229 4 := by decide +kernel
lemma complete_case229 : ∀ e0, CompleteAt 229 e0 := by
  intro e0
  fin_cases e0
  · exact complete_229_0
  · exact complete_229_1
  · exact complete_229_2
  · exact complete_229_3
  · exact complete_229_4
#print axioms complete_case229
end Erdos184Work.PureSixLocalFilter1
